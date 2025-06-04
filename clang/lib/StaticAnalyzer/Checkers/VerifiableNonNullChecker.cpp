#include "Iterator.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"

#include "clang/Analysis/AnyCall.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"

#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Path.h"

using namespace clang;
using namespace ento;

namespace {
const char *getNullabilityString(const Nullability Nullab) {
  switch (Nullab) {
  case Nullability::Nullable:
    return "nullable";
  case Nullability::Nonnull:
    return "nonnull";
  default:
    llvm_unreachable("Unexpected enumeration.");
  }
  return "";
}

static bool isPointerNonnullable(const QualType T) {
  if (auto &&PT = T->getAs<PointerType>()) {
    return T->hasAttr(attr::VerifiableNonNull);
  }
  return false;
}

enum class ErrorKind : int {
  NullptrAssignedToNonnull,
  NullptrPassedToNonnull,
  NullptrReturnedToNonnull,
  NullablePointerAssignedToNonnull,
  NullablePointerReturnedToNonnull,
  NullablePointerDereferenced,
  NullablePointerPassedToNonnull
};

class VerifiableNonNullChecker final
    : public Checker<
          check::Bind, check::PreCall, check::PreStmt<ReturnStmt>,
          check::PostCall, check::PostStmt<ExplicitCastExpr>,
          check::DeadSymbols, eval::Assume, check::Location,
          check::Event<ImplicitNullDerefEvent>, check::BeginFunction,
          check::PreStmt<UnaryOperator>, check::PreStmt<BinaryOperator>,
          check::PreStmt<ArraySubscriptExpr>, check::PreStmt<MemberExpr>> {

public:
  bool NoDiagnoseCallsToSystemHeaders = false;

  void checkBind(SVal L, SVal V, const Stmt *S, CheckerContext &C) const;
  void checkPostStmt(const ExplicitCastExpr *CE, CheckerContext &C) const;
  void checkPreStmt(const ReturnStmt *S, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkDeadSymbols(SymbolReaper &SR, CheckerContext &C) const;
  void checkEvent(const ImplicitNullDerefEvent &Event) const;
  void checkLocation(SVal Location, bool IsLoad, const Stmt *S,
                     CheckerContext &C) const;
  void checkBeginFunction(CheckerContext &Ctx) const;
  ProgramStateRef evalAssume(ProgramStateRef State, SVal Cond,
                             bool Assumption) const;
  void checkPreStmt(const UnaryOperator *UO, CheckerContext &C) const;
  void checkPreStmt(const BinaryOperator *BO, CheckerContext &C) const;
  void checkPreStmt(const ArraySubscriptExpr *ASE, CheckerContext &C) const;
  void checkPreStmt(const MemberExpr *ME, CheckerContext &C) const;
  void verifyAccess(CheckerContext &C, const Expr *E) const;

  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;

  enum CheckKind {
    CK_NullptrPassedToNonnull,
    CK_NullptrReturnedFromNonnull,
    CK_NullablePointerDereferenced,
    CK_NullablePointerPassedToNonnull,
    CK_NullablePointerReturnedFromNonnull,
    CK_NumCheckKinds
  };

  bool ChecksEnabled[CK_NumCheckKinds] = {false};
  CheckerNameRef CheckNames[CK_NumCheckKinds];
  mutable std::unique_ptr<BugType> BTs[CK_NumCheckKinds];

  const std::unique_ptr<BugType> &getBugType(CheckKind Kind) const {
    if (!BTs[Kind])
      BTs[Kind].reset(new BugType(CheckNames[Kind], "Nullability",
                                  categories::MemoryError));
    return BTs[Kind];
  }

  bool NeedTracking = false;

private:
  class NullabilityBugVisitor final : public BugReporterVisitor {
  public:
    explicit NullabilityBugVisitor(const MemRegion *M) : Region(M) {}

    void Profile(llvm::FoldingSetNodeID &ID) const override {
      static int X = 0;
      ID.AddPointer(&X);
      ID.AddPointer(Region);
    }

    PathDiagnosticPieceRef VisitNode(const ExplodedNode *N,
                                     BugReporterContext &BRC,
                                     PathSensitiveBugReport &BR) override;

  private:
    // The tracked region.
    const MemRegion *Region;
  };

  void reportBugIfInvariantHolds(StringRef Msg, ErrorKind Error, CheckKind CK,
                                 ExplodedNode *N, const MemRegion *Region,
                                 CheckerContext &C,
                                 const Stmt *ValueExpr = nullptr,
                                 bool SuppressPath = false) const;

  void reportBug(StringRef Msg, ErrorKind Error, CheckKind CK, ExplodedNode *N,
                 const MemRegion *Region, BugReporter &BR,
                 const Stmt *ValueExpr = nullptr) const {
    const std::unique_ptr<BugType> &BT = getBugType(CK);
    auto R = std::make_unique<PathSensitiveBugReport>(*BT, Msg, N);
    if (Region) {
      R->markInteresting(Region);
      R->addVisitor<NullabilityBugVisitor>(Region);
    }
    if (ValueExpr) {
      R->addRange(ValueExpr->getSourceRange());
      if (Error == ErrorKind::NullptrAssignedToNonnull ||
          Error == ErrorKind::NullptrPassedToNonnull ||
          Error == ErrorKind::NullptrReturnedToNonnull)
        if (const auto *Ex = dyn_cast<Expr>(ValueExpr))
          bugreporter::trackExpressionValue(N, Ex, *R);
    }
    BR.emitReport(std::move(R));
  }

  const SymbolicRegion *getTrackRegion(SVal Val,
                                       bool CheckSuperRegion = false) const;

  bool isDiagnosableCall(const CallEvent &Call) const {
    if (NoDiagnoseCallsToSystemHeaders && Call.isInSystemHeader())
      return false;

    return true;
  }
};

class NullabilityState {
public:
  NullabilityState(const Nullability Nullab, const Stmt *Source = nullptr)
      : Nullab(Nullab), Source(Source) {}

  const Stmt *getNullabilitySource() const { return Source; }

  Nullability getValue() const { return Nullab; }

  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddInteger(static_cast<char>(Nullab));
    ID.AddPointer(Source);
  }

  void print(raw_ostream &Out) const {
    Out << getNullabilityString(Nullab) << "\n";
  }

private:
  Nullability Nullab;
  const Stmt *Source;
};

bool operator==(const NullabilityState Lhs, const NullabilityState Rhs) {
  return Lhs.getValue() == Rhs.getValue() &&
         Lhs.getNullabilitySource() == Rhs.getNullabilitySource();
}

using ObjectPropPair = std::pair<const MemRegion *, const IdentifierInfo *>;

struct ConstrainedPropertyVal {
  DefinedOrUnknownSVal Value;

  bool isConstrainedNonnull;

  ConstrainedPropertyVal(const DefinedOrUnknownSVal SV)
      : Value(SV), isConstrainedNonnull(false) {}

  void Profile(llvm::FoldingSetNodeID &ID) const {
    Value.Profile(ID);
    ID.AddInteger(isConstrainedNonnull ? 1 : 0);
  }
};

bool operator==(const ConstrainedPropertyVal &Lhs,
                const ConstrainedPropertyVal &Rhs) {
  return Lhs.Value == Rhs.Value &&
         Lhs.isConstrainedNonnull == Rhs.isConstrainedNonnull;
}

} // end anonymous namespace

REGISTER_MAP_WITH_PROGRAMSTATE(NullabilityMap, const MemRegion *,
                               NullabilityState)
REGISTER_MAP_WITH_PROGRAMSTATE(PropertyAccessesMap, ObjectPropPair,
                               ConstrainedPropertyVal)

REGISTER_TRAIT_WITH_PROGRAMSTATE(InvariantViolated, bool)

enum class NullConstraint { IsNull, IsNotNull, Unknown };

static NullConstraint getNullConstraint(const DefinedOrUnknownSVal Val,
                                        const ProgramStateRef &State) {
  const ConditionTruthVal Nullness = State->isNull(Val);
  if (Nullness.isConstrainedFalse())
    return NullConstraint::IsNotNull;
  if (Nullness.isConstrainedTrue())
    return NullConstraint::IsNull;
  return NullConstraint::Unknown;
}

static bool isValidPointerType(QualType T) {
  return T->isAnyPointerType() || T->isBlockPointerType();
}

const SymbolicRegion *
VerifiableNonNullChecker::getTrackRegion(const SVal Val,
                                         const bool CheckSuperRegion) const {
  if (!NeedTracking)
    return nullptr;

  const auto RegionSVal = Val.getAs<loc::MemRegionVal>();
  if (!RegionSVal)
    return nullptr;

  const MemRegion *Region = RegionSVal->getRegion();

  if (CheckSuperRegion) {
    if (const SubRegion *FieldReg = Region->getAs<FieldRegion>()) {
      if (const auto *ER = dyn_cast<ElementRegion>(FieldReg->getSuperRegion()))
        FieldReg = ER;
      return dyn_cast<SymbolicRegion>(FieldReg->getSuperRegion());
    }
    if (const auto *ElementReg = Region->getAs<ElementRegion>())
      return dyn_cast<SymbolicRegion>(ElementReg->getSuperRegion());
  }

  return dyn_cast<SymbolicRegion>(Region);
}

PathDiagnosticPieceRef
VerifiableNonNullChecker::NullabilityBugVisitor::VisitNode(
    const ExplodedNode *N, BugReporterContext &BRC,
    PathSensitiveBugReport &BR) {
  const ProgramStateRef State = N->getState();
  const ProgramStateRef StatePrev = N->getFirstPred()->getState();

  const NullabilityState *TrackedNullab = State->get<NullabilityMap>(Region);
  const NullabilityState *TrackedNullabPrev =
      StatePrev->get<NullabilityMap>(Region);
  if (!TrackedNullab)
    return nullptr;

  if (TrackedNullabPrev &&
      TrackedNullabPrev->getValue() == TrackedNullab->getValue())
    return nullptr;

  const Stmt *S = TrackedNullab->getNullabilitySource();
  if (!S || S->getBeginLoc().isInvalid()) {
    S = N->getStmtForDiagnostics();
  }

  if (!S)
    return nullptr;

  std::string InfoText =
      (llvm::Twine("Nullability '") +
       getNullabilityString(TrackedNullab->getValue()) + "' is inferred")
          .str();

  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, InfoText, true);
}

static Nullability getNullabilityFromAttributes(QualType T) {
  const auto *AttrType = T->getAs<AttributedType>();
  if (!AttrType)
    return Nullability::Nullable;
  if (AttrType->getAttrKind() == attr::VerifiableNonNull)
    return Nullability::Nonnull;
  return Nullability::Nullable;
}

static bool checkValueAtLValForInvariantViolation(const ProgramStateRef &State,
                                                  const SVal LV, QualType T) {
  if (!isPointerNonnullable(T))
    return false;

  const auto RegionVal = LV.getAs<loc::MemRegionVal>();
  if (!RegionVal)
    return false;

  auto StoredVal = State->getSVal(*RegionVal).getAs<loc::MemRegionVal>();
  if (!StoredVal || !isa<SymbolicRegion>(StoredVal->getRegion()))
    return false;

  if (getNullConstraint(*StoredVal, State) == NullConstraint::IsNull)
    return true;

  return false;
}

static bool
checkParamsForPreconditionViolation(const ArrayRef<ParmVarDecl *> Params,
                                    const ProgramStateRef &State,
                                    const LocationContext *LocCtxt) {
  for (const auto *ParamDecl : Params) {
    if (ParamDecl->isParameterPack())
      break;

    if (const SVal LV = State->getLValue(ParamDecl, LocCtxt);
        checkValueAtLValForInvariantViolation(State, LV,
                                              ParamDecl->getType())) {
      return true;
    }
  }
  return false;
}

static bool
checkSelfIvarsForInvariantViolation(const ProgramStateRef &State,
                                    const LocationContext *LocCtxt) {
  if (auto *MD = dyn_cast<ObjCMethodDecl>(LocCtxt->getDecl());
      !MD || !MD->isInstanceMethod())
    return false;

  const ImplicitParamDecl *SelfDecl = LocCtxt->getSelfDecl();
  if (!SelfDecl)
    return false;

  const SVal SelfVal = State->getSVal(State->getRegion(SelfDecl, LocCtxt));

  const ObjCObjectPointerType *SelfType =
      dyn_cast<ObjCObjectPointerType>(SelfDecl->getType());
  if (!SelfType)
    return false;

  const ObjCInterfaceDecl *ID = SelfType->getInterfaceDecl();
  if (!ID)
    return false;

  for (const auto *IvarDecl : ID->ivars()) {
    SVal LV = State->getLValue(IvarDecl, SelfVal);
    if (checkValueAtLValForInvariantViolation(State, LV, IvarDecl->getType())) {
      return true;
    }
  }
  return false;
}

static bool checkInvariantViolation(const ProgramStateRef &State,
                                    ExplodedNode *N, CheckerContext &C) {
  if (State->get<InvariantViolated>())
    return true;

  const LocationContext *LocCtxt = C.getLocationContext();
  const Decl *D = LocCtxt->getDecl();
  if (!D)
    return false;

  ArrayRef<ParmVarDecl *> Params;
  if (const auto *BD = dyn_cast<BlockDecl>(D))
    Params = BD->parameters();
  else if (const auto *FD = dyn_cast<FunctionDecl>(D))
    Params = FD->parameters();
  else if (const auto *MD = dyn_cast<ObjCMethodDecl>(D))
    Params = MD->parameters();
  else
    return false;

  if (checkParamsForPreconditionViolation(Params, State, LocCtxt) ||
      checkSelfIvarsForInvariantViolation(State, LocCtxt)) {
    if (!N->isSink())
      C.addTransition(State->set<InvariantViolated>(true), N);
    return true;
  }
  return false;
}

void VerifiableNonNullChecker::reportBugIfInvariantHolds(
    const StringRef Msg, const ErrorKind Error, const CheckKind CK,
    ExplodedNode *N, const MemRegion *Region, CheckerContext &C,
    const Stmt *ValueExpr, const bool SuppressPath) const {
  ProgramStateRef OriginalState = N->getState();

  if (checkInvariantViolation(OriginalState, N, C)) {
    return;
  }

  if (SuppressPath) {
    OriginalState = OriginalState->set<InvariantViolated>(true);
    N = C.addTransition(OriginalState, N);
  }

  reportBug(Msg, Error, CK, N, Region, C.getBugReporter(), ValueExpr);
}

void VerifiableNonNullChecker::checkDeadSymbols(SymbolReaper &SR,
                                                CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  NullabilityMapTy Nullabilities = State->get<NullabilityMap>();
  for (const MemRegion *Reg : llvm::make_first_range(Nullabilities)) {
    const auto *Region = Reg->getAs<SymbolicRegion>();
    assert(Region && "Non-symbolic region is tracked.");
    if (SR.isDead(Region->getSymbol())) {
      State = State->remove<NullabilityMap>(Reg);
    }
  }

  PropertyAccessesMapTy PropertyAccesses = State->get<PropertyAccessesMap>();
  for (const ObjectPropPair PropKey :
       llvm::make_first_range(PropertyAccesses)) {
    if (const MemRegion *ReceiverRegion = PropKey.first;
        !SR.isLiveRegion(ReceiverRegion)) {
      State = State->remove<PropertyAccessesMap>(PropKey);
    }
  }

  if (checkInvariantViolation(State, C.getPredecessor(), C))
    return;
  C.addTransition(State);
}

void VerifiableNonNullChecker::checkEvent(
    const ImplicitNullDerefEvent &Event) const {
  if (Event.SinkNode->getState()->get<InvariantViolated>())
    return;

  const MemRegion *Region =
      getTrackRegion(Event.Location, /*CheckSuperRegion=*/true);
  if (!Region)
    return;

  const ProgramStateRef State = Event.SinkNode->getState();
  const NullabilityState *TrackedNullability =
      State->get<NullabilityMap>(Region);

  if (!TrackedNullability)
    return;

  if (ChecksEnabled[CK_NullablePointerDereferenced] &&
      TrackedNullability->getValue() == Nullability::Nullable) {
    BugReporter &BR = *Event.BR;
    if (Event.IsDirectDereference)
      reportBug("Nullable pointer is dereferenced",
                ErrorKind::NullablePointerDereferenced,
                CK_NullablePointerDereferenced, Event.SinkNode, Region, BR);
    else {
      reportBug("Nullable pointer is passed to a callee that requires a "
                "non-null",
                ErrorKind::NullablePointerPassedToNonnull,
                CK_NullablePointerDereferenced, Event.SinkNode, Region, BR);
    }
  }
}

void VerifiableNonNullChecker::checkBeginFunction(CheckerContext &C) const {
  if (!C.inTopFrame())
    return;

  const LocationContext *LCtx = C.getLocationContext();
  const auto AbstractCall = AnyCall::forDecl(LCtx->getDecl());
  if (!AbstractCall || AbstractCall->parameters().empty())
    return;

  ProgramStateRef State = C.getState();
  for (const ParmVarDecl *Param : AbstractCall->parameters()) {
    if (!isValidPointerType(Param->getType()))
      continue;

    Nullability RequiredNullability =
        getNullabilityFromAttributes(Param->getType());

    if (isPointerNonnullable(Param->getType()))
      continue;
    const VarRegion *ParamRegion = State->getRegion(Param, LCtx);
    const MemRegion *ParamPointeeRegion =
        State->getSVal(ParamRegion).getAsRegion();
    if (!ParamPointeeRegion)
      continue;

    State = State->set<NullabilityMap>(ParamPointeeRegion,
                                       NullabilityState(RequiredNullability));
  }
  C.addTransition(State);
}

void VerifiableNonNullChecker::checkLocation(SVal Location, bool IsLoad,
                                             const Stmt *S,
                                             CheckerContext &Context) const {
  if (!IsLoad)
    return;
  const auto *Region =
      dyn_cast_or_null<TypedValueRegion>(Location.getAsRegion());
  if (!Region)
    return;

  ProgramStateRef State = Context.getState();

  auto StoredVal = State->getSVal(Region).getAs<loc::MemRegionVal>();
  if (!StoredVal)
    return;
  if (isPointerNonnullable(Region->getValueType())) {
    if (ProgramStateRef NewState = State->assume(*StoredVal, true)) {
      Context.addTransition(NewState);
    }
  }
}

static const Expr *lookThroughImplicitCasts(const Expr *E) {
  return E->IgnoreImpCasts();
}

void VerifiableNonNullChecker::checkPreStmt(const ReturnStmt *S,
                                            CheckerContext &C) const {
  const auto RetExpr = S->getRetValue();
  if (!RetExpr)
    return;

  if (!isValidPointerType(RetExpr->getType()))
    return;

  ProgramStateRef State = C.getState();
  if (State->get<InvariantViolated>())
    return;

  const auto RetSVal = C.getSVal(S).getAs<DefinedOrUnknownSVal>();
  if (!RetSVal)
    return;

  bool InSuppressedMethodFamily = false;

  QualType RequiredRetType;
  AnalysisDeclContext *DeclCtxt =
      C.getLocationContext()->getAnalysisDeclContext();
  const Decl *D = DeclCtxt->getDecl();
  if (auto *MD = dyn_cast<ObjCMethodDecl>(D)) {
    if (const ObjCMethodFamily Family = MD->getMethodFamily();
        OMF_init == Family || OMF_copy == Family || OMF_mutableCopy == Family)
      InSuppressedMethodFamily = true;

    RequiredRetType = MD->getReturnType();
  } else if (auto *FD = dyn_cast<FunctionDecl>(D)) {
    RequiredRetType = FD->getReturnType();
  } else {
    return;
  }

  const NullConstraint Nullness = getNullConstraint(*RetSVal, State);

  Nullability RequiredNullability =
      getNullabilityFromAttributes(RequiredRetType);
  if (const auto *FunDecl = C.getLocationContext()->getDecl();
      FunDecl && FunDecl->getAttr<ReturnsNonNullAttr>() &&
      (RequiredNullability == Nullability::Unspecified ||
       RequiredNullability == Nullability::Nullable)) {
    RequiredNullability = Nullability::Nonnull;
  }

  const Nullability RetExprTypeLevelNullability = getNullabilityFromAttributes(
      lookThroughImplicitCasts(RetExpr)->getType());

  const bool NullReturnedFromNonNull =
      RequiredNullability == Nullability::Nonnull &&
      Nullness == NullConstraint::IsNull;
  if (ChecksEnabled[CK_NullptrReturnedFromNonnull] && NullReturnedFromNonNull &&
      RetExprTypeLevelNullability != Nullability::Nonnull &&
      !InSuppressedMethodFamily) {
    static CheckerProgramPointTag Tag(this, "NullReturnedFromNonnull");
    ExplodedNode *N = C.generateErrorNode(State, &Tag);
    if (!N)
      return;

    SmallString<256> SBuf;
    llvm::raw_svector_ostream OS(SBuf);
    OS << "Nullptr returned from a " << C.getDeclDescription(D)
       << " that is expected to return a non-null value";
    reportBugIfInvariantHolds(OS.str(), ErrorKind::NullptrReturnedToNonnull,
                              CK_NullptrReturnedFromNonnull, N, nullptr, C,
                              RetExpr);
    return;
  }

  if (NullReturnedFromNonNull) {
    State = State->set<InvariantViolated>(true);
    C.addTransition(State);
    return;
  }

  const MemRegion *Region = getTrackRegion(*RetSVal);
  if (!Region)
    return;

  const NullabilityState *TrackedNullability =
      State->get<NullabilityMap>(Region);
  if (TrackedNullability) {
    if (const Nullability TrackedNullabValue = TrackedNullability->getValue();
        ChecksEnabled[CK_NullablePointerReturnedFromNonnull] &&
        Nullness != NullConstraint::IsNotNull &&
        TrackedNullabValue == Nullability::Nullable &&
        RequiredNullability == Nullability::Nonnull) {
      static CheckerProgramPointTag Tag(this, "NullableReturnedFromNonnull");
      ExplodedNode *N = C.addTransition(State, C.getPredecessor(), &Tag);

      SmallString<256> SBuf;
      llvm::raw_svector_ostream OS(SBuf);
      OS << "Nullable pointer is returned from a " << C.getDeclDescription(D)
         << " that is expected to return a non-null value";

      reportBugIfInvariantHolds(
          OS.str(), ErrorKind::NullablePointerReturnedToNonnull,
          CK_NullablePointerReturnedFromNonnull, N, Region, C);
    }
    return;
  }
  if (RequiredNullability == Nullability::Nullable) {
    State = State->set<NullabilityMap>(
        Region, NullabilityState(RequiredNullability, S));
    C.addTransition(State);
  }
}

void VerifiableNonNullChecker::checkPreCall(const CallEvent &Call,
                                            CheckerContext &C) const {
  if (!Call.getDecl())
    return;

  const ProgramStateRef State = C.getState();
  if (State->get<InvariantViolated>())
    return;

  const ProgramStateRef OrigState = State;

  unsigned Idx = 0;
  for (const ParmVarDecl *Param : Call.parameters()) {
    if (Param->isParameterPack())
      break;

    if (Idx >= Call.getNumArgs())
      break;

    const Expr *ArgExpr = Call.getArgExpr(Idx);
    auto ArgSVal = Call.getArgSVal(Idx++).getAs<DefinedOrUnknownSVal>();
    if (!ArgSVal)
      continue;

    if (!isValidPointerType(Param->getType()) &&
        !Param->getType()->isReferenceType())
      continue;

    const NullConstraint Nullness = getNullConstraint(*ArgSVal, State);

    const Nullability RequiredNullability =
        getNullabilityFromAttributes(Param->getType());
    const Nullability ArgExprTypeLevelNullability =
        getNullabilityFromAttributes(
            lookThroughImplicitCasts(ArgExpr)->getType());

    const unsigned ParamIdx = Param->getFunctionScopeIndex() + 1;

    if (ChecksEnabled[CK_NullptrPassedToNonnull] &&
        Nullness == NullConstraint::IsNull &&
        ArgExprTypeLevelNullability != Nullability::Nonnull &&
        RequiredNullability == Nullability::Nonnull &&
        isDiagnosableCall(Call)) {
      ExplodedNode *N = C.generateErrorNode(State);
      if (!N)
        return;

      SmallString<256> SBuf;
      llvm::raw_svector_ostream OS(SBuf);
      OS << "Nullptr passed to a callee that requires a non-null " << ParamIdx
         << llvm::getOrdinalSuffix(ParamIdx) << " parameter";
      reportBugIfInvariantHolds(OS.str(), ErrorKind::NullptrPassedToNonnull,
                                CK_NullptrPassedToNonnull, N, nullptr, C,
                                ArgExpr,
                                /*SuppressPath=*/false);
      return;
    }

    const MemRegion *Region = getTrackRegion(*ArgSVal);
    if (!Region)
      continue;

    const NullabilityState *TrackedNullability =
        State->get<NullabilityMap>(Region);

    if (TrackedNullability) {
      if (Nullness == NullConstraint::IsNotNull ||
          TrackedNullability->getValue() != Nullability::Nullable)
        continue;

      if (ChecksEnabled[CK_NullablePointerPassedToNonnull] &&
          RequiredNullability == Nullability::Nonnull &&
          isDiagnosableCall(Call)) {
        ExplodedNode *N = C.addTransition(State);
        SmallString<256> SBuf;
        llvm::raw_svector_ostream OS(SBuf);
        OS << "Nullable pointer is passed to a callee that requires a non-null "
           << ParamIdx << llvm::getOrdinalSuffix(ParamIdx) << " parameter";
        reportBugIfInvariantHolds(OS.str(),
                                  ErrorKind::NullablePointerPassedToNonnull,
                                  CK_NullablePointerPassedToNonnull, N, Region,
                                  C, ArgExpr, /*SuppressPath=*/true);
        return;
      }
      if (ChecksEnabled[CK_NullablePointerDereferenced] &&
          Param->getType()->isReferenceType()) {
        ExplodedNode *N = C.addTransition(State);
        reportBugIfInvariantHolds("Nullable pointer is dereferenced",
                                  ErrorKind::NullablePointerDereferenced,
                                  CK_NullablePointerDereferenced, N, Region, C,
                                  ArgExpr, /*SuppressPath=*/true);
        return;
      }
    }
  }
  if (State != OrigState)
    C.addTransition(State);
}

void VerifiableNonNullChecker::checkPostCall(const CallEvent &Call,
                                             CheckerContext &C) const {
  const auto *Decl = Call.getDecl();
  if (!Decl)
    return;
  if (Call.getKind() == CE_ObjCMessage)
    return;
  const FunctionType *FuncType = Decl->getFunctionType();
  if (!FuncType)
    return;
  QualType ReturnType = FuncType->getReturnType();
  if (!isValidPointerType(ReturnType))
    return;
  ProgramStateRef State = C.getState();
  if (State->get<InvariantViolated>())
    return;

  const MemRegion *Region = getTrackRegion(Call.getReturnValue());
  if (!Region)
    return;

  const SourceManager &SM = C.getSourceManager();
  if (const StringRef FilePath =
          SM.getFilename(SM.getSpellingLoc(Decl->getBeginLoc()));
      llvm::sys::path::filename(FilePath).starts_with("CG")) {
    State = State->set<NullabilityMap>(Region, Nullability::Contradicted);
    C.addTransition(State);
    return;
  }

  const NullabilityState *TrackedNullability =
      State->get<NullabilityMap>(Region);

  if (const Expr *E = Call.getOriginExpr())
    ReturnType = E->getType();

  if (!TrackedNullability &&
      getNullabilityFromAttributes(ReturnType) == Nullability::Nullable) {
    State = State->set<NullabilityMap>(Region, Nullability::Nullable);
    C.addTransition(State);
  }
}

ProgramStateRef VerifiableNonNullChecker::evalAssume(ProgramStateRef State,
                                                     SVal Cond,
                                                     bool Assumption) const {
  const PropertyAccessesMapTy PropertyAccesses =
      State->get<PropertyAccessesMap>();
  for (auto [PropKey, PropVal] : PropertyAccesses) {
    if (!PropVal.isConstrainedNonnull) {
      if (ConditionTruthVal IsNonNull = State->isNonNull(PropVal.Value);
          IsNonNull.isConstrainedTrue()) {
        ConstrainedPropertyVal Replacement = PropVal;
        Replacement.isConstrainedNonnull = true;
        State = State->set<PropertyAccessesMap>(PropKey, Replacement);
      } else if (IsNonNull.isConstrainedFalse()) {
        State = State->remove<PropertyAccessesMap>(PropKey);
      }
    }
  }

  return State;
}

void VerifiableNonNullChecker::checkPostStmt(const ExplicitCastExpr *CE,
                                             CheckerContext &C) const {
  const QualType OriginType = CE->getSubExpr()->getType();
  const QualType DestType = CE->getType();
  if (!isValidPointerType(OriginType))
    return;
  if (!isValidPointerType(DestType))
    return;

  ProgramStateRef State = C.getState();
  if (State->get<InvariantViolated>())
    return;

  const Nullability DestNullability = getNullabilityFromAttributes(DestType);

  if (DestNullability == Nullability::Unspecified)
    return;

  const auto RegionSVal = C.getSVal(CE).getAs<DefinedOrUnknownSVal>();
  const MemRegion *Region = getTrackRegion(*RegionSVal);
  if (!Region)
    return;

  if (DestNullability == Nullability::Nonnull) {
    if (const NullConstraint Nullness = getNullConstraint(*RegionSVal, State);
        Nullness == NullConstraint::IsNull) {
      State = State->set<NullabilityMap>(Region, Nullability::Contradicted);
      C.addTransition(State);
      return;
    }
  }

  const NullabilityState *TrackedNullability =
      State->get<NullabilityMap>(Region);

  if (!TrackedNullability) {
    if (DestNullability != Nullability::Nullable)
      return;
    State = State->set<NullabilityMap>(Region,
                                       NullabilityState(DestNullability, CE));
    C.addTransition(State);
    return;
  }

  if (TrackedNullability->getValue() != DestNullability &&
      TrackedNullability->getValue() != Nullability::Contradicted) {
    State = State->set<NullabilityMap>(Region, Nullability::Contradicted);
    C.addTransition(State);
  }
}

static const Expr *matchValueExprForBind(const Stmt *S) {
  if (auto *BinOp = dyn_cast<BinaryOperator>(S)) {
    if (BinOp->getOpcode() == BO_Assign)
      return BinOp->getRHS();
  }

  if (auto *DS = dyn_cast<DeclStmt>(S)) {
    if (DS->isSingleDecl()) {
      auto *VD = dyn_cast<VarDecl>(DS->getSingleDecl());
      if (!VD)
        return nullptr;

      if (const Expr *Init = VD->getInit())
        return Init;
    }
  }

  return nullptr;
}

void VerifiableNonNullChecker::checkBind(SVal L, SVal V, const Stmt *S,
                                         CheckerContext &C) const {
  const TypedValueRegion *TVR =
      dyn_cast_or_null<TypedValueRegion>(L.getAsRegion());
  if (!TVR)
    return;

  const QualType LocType = TVR->getValueType();
  if (!isValidPointerType(LocType))
    return;

  ProgramStateRef State = C.getState();
  if (State->get<InvariantViolated>())
    return;

  const auto ValDefOrUnknown = V.getAs<DefinedOrUnknownSVal>();
  if (!ValDefOrUnknown)
    return;

  const NullConstraint RhsNullness = getNullConstraint(*ValDefOrUnknown, State);

  auto ValNullability = Nullability::Nullable;
  if (const SymbolRef Sym = ValDefOrUnknown->getAsSymbol())
    ValNullability = getNullabilityFromAttributes(Sym->getType());

  const Nullability LocNullability = getNullabilityFromAttributes(LocType);
  auto ValueExprTypeLevelNullability = Nullability::Nullable;
  const Expr *ValueExpr = matchValueExprForBind(S);
  if (ValueExpr) {
    ValueExprTypeLevelNullability = getNullabilityFromAttributes(
        lookThroughImplicitCasts(ValueExpr)->getType());
  }

  const bool NullAssignedToNonNull = LocNullability == Nullability::Nonnull &&
                                     RhsNullness == NullConstraint::IsNull;

  if (ChecksEnabled[CK_NullptrPassedToNonnull] && NullAssignedToNonNull &&
      ValNullability != Nullability::Nonnull &&
      ValueExprTypeLevelNullability != Nullability::Nonnull) {

    static CheckerProgramPointTag Tag(this, "NullPassedToNonnull");
    ExplodedNode *N = C.generateErrorNode(State, &Tag);
    if (!N)
      return;

    const Stmt *ValueStmt = S;
    if (ValueExpr)
      ValueStmt = ValueExpr;

    SmallString<256> SBuf;
    llvm::raw_svector_ostream OS(SBuf);
    OS << "Nullptr assigned to a pointer which is expected to have non-null "
          "value";
    reportBugIfInvariantHolds(OS.str(), ErrorKind::NullptrAssignedToNonnull,
                              CK_NullptrPassedToNonnull, N, nullptr, C,
                              ValueStmt);
    return;
  }

  if (NullAssignedToNonNull) {
    State = State->set<InvariantViolated>(true);
    C.addTransition(State);
    return;
  }

  const MemRegion *ValueRegion = getTrackRegion(*ValDefOrUnknown);
  if (!ValueRegion)
    return;

  const NullabilityState *TrackedNullability =
      State->get<NullabilityMap>(ValueRegion);

  if (TrackedNullability) {
    if (RhsNullness == NullConstraint::IsNotNull ||
        TrackedNullability->getValue() != Nullability::Nullable)
      return;
    if (ChecksEnabled[CK_NullablePointerPassedToNonnull] &&
        LocNullability == Nullability::Nonnull) {
      static CheckerProgramPointTag Tag(this, "NullablePassedToNonnull");
      ExplodedNode *N = C.addTransition(State, C.getPredecessor(), &Tag);
      reportBugIfInvariantHolds("Nullable pointer is assigned to a pointer "
                                "which is expected to have non-null value",
                                ErrorKind::NullablePointerAssignedToNonnull,
                                CK_NullablePointerPassedToNonnull, N,
                                ValueRegion, C);
    }
    return;
  }

  const auto *BinOp = dyn_cast<BinaryOperator>(S);

  if (ValNullability == Nullability::Nullable) {
    const Stmt *NullabilitySource = BinOp ? BinOp->getRHS() : S;
    State = State->set<NullabilityMap>(
        ValueRegion, NullabilityState(ValNullability, NullabilitySource));
    C.addTransition(State);
    return;
  }

  if (LocNullability == Nullability::Nullable) {
    const Stmt *NullabilitySource = BinOp ? BinOp->getLHS() : S;
    State = State->set<NullabilityMap>(
        ValueRegion, NullabilityState(LocNullability, NullabilitySource));
    C.addTransition(State);
  }
}

void VerifiableNonNullChecker::checkPreStmt(const UnaryOperator *UO,
                                            CheckerContext &C) const {
  if (isa<CXXThisExpr>(UO->getSubExpr()))
    return;
  UnaryOperatorKind OK = UO->getOpcode();
  if (clang::ento::iterator::isAccessOperator(OK)) {
    verifyAccess(C, UO->getSubExpr());
  }
}

void VerifiableNonNullChecker::checkPreStmt(const BinaryOperator *BO,
                                            CheckerContext &C) const {
  BinaryOperatorKind OK = BO->getOpcode();
  if (clang::ento::iterator::isAccessOperator(OK)) {
    verifyAccess(C, BO->getLHS());
  }
}

void VerifiableNonNullChecker::checkPreStmt(const ArraySubscriptExpr *ASE,
                                            CheckerContext &C) const {
  verifyAccess(C, ASE->getLHS());
}

void VerifiableNonNullChecker::checkPreStmt(const MemberExpr *ME,
                                            CheckerContext &C) const {
  if (!ME->isArrow() || ME->isImplicitAccess())
    return;
  verifyAccess(C, ME->getBase());
}

void VerifiableNonNullChecker::verifyAccess(CheckerContext &C,
                                            const Expr *E) const {
  if (isPointerNonnullable(E->getType()))
    return;
  const ProgramStateRef State = C.getState();
  const SVal Val = State->getSVal(E, C.getLocationContext());

  const auto DefOrUnknown = Val.getAs<DefinedOrUnknownSVal>();
  if (!DefOrUnknown)
    return;
  if (State->isNonNull(*DefOrUnknown).isConstrainedTrue())
    return;

  static CheckerProgramPointTag Tag(this, "NullablePointerDereferenced");
  ExplodedNode *N = C.generateErrorNode(State, &Tag);
  if (!N)
    return;

  const MemRegion *Region = getTrackRegion(*DefOrUnknown);
  if (!Region)
    return;

  reportBug("Nullable pointer is dereferenced",
            ErrorKind::NullablePointerDereferenced,
            CK_NullablePointerDereferenced, N, Region, C.getBugReporter());
}

void VerifiableNonNullChecker::printState(raw_ostream &Out,
                                          const ProgramStateRef State,
                                          const char *NL,
                                          const char *Sep) const {

  const NullabilityMapTy B = State->get<NullabilityMap>();

  if (State->get<InvariantViolated>())
    Out << Sep << NL
        << "Nullability invariant was violated, warnings suppressed." << NL;

  if (B.isEmpty())
    return;

  if (!State->get<InvariantViolated>())
    Out << Sep << NL;

  for (auto [Region, State] : B) {
    Out << Region << " : ";
    State.print(Out);
    Out << NL;
  }
}

void ento::registerVerifiableNonNullChecker(CheckerManager &mgr) {
  mgr.registerChecker<VerifiableNonNullChecker>();
}

bool ento::shouldRegisterVerifiableNonNullChecker(CheckerManager const &) {
  return true;
}

#define REGISTER_VERIFIABLE_NONNULL_CHECKER(CHECKER_NAME,                      \
                                            IS_TRACKING_REQUIRED)              \
  void ento::register##CHECKER_NAME##Checker(CheckerManager &mgr) {            \
    VerifiableNonNullChecker *checker =                                        \
        mgr.getChecker<VerifiableNonNullChecker>();                            \
    checker->ChecksEnabled[VerifiableNonNullChecker::CK_##CHECKER_NAME] =      \
        true;                                                                  \
    checker->CheckNames[VerifiableNonNullChecker::CK_##CHECKER_NAME] =         \
        mgr.getCurrentCheckerName();                                           \
    checker->NeedTracking = checker->NeedTracking || IS_TRACKING_REQUIRED;     \
    checker->NoDiagnoseCallsToSystemHeaders =                                  \
        checker->NoDiagnoseCallsToSystemHeaders;                               \
  }                                                                            \
                                                                               \
  bool ento::shouldRegister##CHECKER_NAME##Checker(                            \
      const CheckerManager &mgr) {                                             \
    return true;                                                               \
  }

REGISTER_VERIFIABLE_NONNULL_CHECKER(NullptrPassedToNonnull, false)
REGISTER_VERIFIABLE_NONNULL_CHECKER(NullptrReturnedFromNonnull, false)

REGISTER_VERIFIABLE_NONNULL_CHECKER(NullablePointerDereferenced, true)
REGISTER_VERIFIABLE_NONNULL_CHECKER(NullablePointerPassedToNonnull, true)
REGISTER_VERIFIABLE_NONNULL_CHECKER(NullablePointerReturnedFromNonnull, true)
