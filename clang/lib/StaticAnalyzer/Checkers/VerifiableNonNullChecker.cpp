#include "Iterator.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ExecutionEngine/GenericValue.h"

using namespace clang;
using namespace ento;

#if 0
namespace {
using namespace clang;
using namespace ento;

class VerifiableNonNullDereferenceChecker final
    : public Checker<check::PreStmt<UnaryOperator>,
                     check::PreStmt<BinaryOperator>, check::PreStmt<MemberExpr>,
                     check::PreStmt<ArraySubscriptExpr>> {
public:
  CheckerNameRef CheckerName;
  mutable std::unique_ptr<BugType> BT;

  [[maybe_unused]] void checkPreStmt(const UnaryOperator *UO,
                                     CheckerContext &C) const {
    // ignore this dereference
    if (isa<CXXThisExpr>(UO->getSubExpr()))
      return;

    if (iterator::isAccessOperator(UO->getOpcode())) {
      verifyAccess(C, UO->getSubExpr());
    }
  }
  [[maybe_unused]] void checkPreStmt(const BinaryOperator *BO,
                                     CheckerContext &C) const {
    llvm::dbgs() << "checkPreStmt(const BinaryOperator *BO, CheckerContext &C)"
                 << '\n';
    if (iterator::isAccessOperator(BO->getOpcode())) {
      llvm::dbgs() << "access operator" << '\n';
      verifyAccess(C, BO->getLHS()); // TODO: check 8[a]
    }
  }

  [[maybe_unused]] void checkPreStmt(const MemberExpr *M,
                                     CheckerContext &C) const {
    llvm::dbgs() << "checkPreStmt(const MemberExpr *M, CheckerContext &C)"
                 << '\n';
    if (M->isArrow()) {
      verifyAccess(C, M->getBase());
    }
  }

  [[maybe_unused]] void checkPreStmt(const ArraySubscriptExpr *AS,
                                     CheckerContext &C) const {
    llvm::dbgs()
        << "checkPreStmt(const ArraySubscriptExpr *AS, CheckerContext &C)"
        << '\n';

    if (AS->getLHS()->getType()->getAs<PointerType>()) // LHS is pointer
      verifyAccess(C, AS->getLHS());
    else
      verifyAccess(C, AS->getRHS()); // handle: 8[ptr]; // idk valid or not))
  }

private:
  const std::unique_ptr<BugType> &getBugType() const {
    if (!BT)
      BT.reset(new BugType(CheckerName, "TODO", categories::MemoryError));
    return BT;
  }

  void reportBug(StringRef M, ExplodedNode *N, BugReporter &BR) const {
    auto &&BT = getBugType();
    auto &&R = std::make_unique<PathSensitiveBugReport>(*BT, M, N);
    BR.emitReport(std::move(R));
  }

  void verifyAccess(CheckerContext &C, const Expr *E) const {
    llvm::dbgs() << "verifyAccess(CheckerContext &C, const Expr *E)" << '\n';
    llvm::dbgs() << "Expr = ";
    E->dump();

    if (pointeeIsVerifiableNonNull(
            E->getType())) // FIXME: rewrite pointeeIsVerifiableNonNull
      return;

    static CheckerProgramPointTag Tag(this, "VerifiableNonNullChecker");

    auto &&S = C.getState();
    auto &&V = S->getSVal(E, C.getLocationContext());

    llvm::dbgs() << "V = " << V << SVal::SValKind::UndefinedValKind << '\n';

    auto &&DefOrUnknown = V.getAs<DefinedOrUnknownSVal>();
    if (!DefOrUnknown) {
      llvm::dbgs() << "!DefOrUnknown" << '\n';

      auto &&N = C.generateErrorNode(S, &Tag);
      if (!N)
        return;
      auto &&BR = C.getBugReporter();
      reportBug(
          "Nullable pointer is dereferenced without a preceding check for "
          "nullptr",
          N, BR);

      return;
    }

    if (S->isNonNull(*DefOrUnknown).isConstrainedTrue()) {
      llvm::dbgs() << "S->isNonNull(*DefOrUnknown).isConstrainedTrue()" << '\n';
      return;
    }

    auto &&N = C.generateErrorNode(S, &Tag);
    if (!N)
      return;
    auto &&BR = C.getBugReporter();
    reportBug("Nullable pointer is dereferenced without a preceding check for "
              "nullptr",
              N, BR);
  }
};
} // namespace
#endif

namespace {
// TODO : rm it
#define STRINGIFY_DETAIL(x) #x
#define STRINGIFY(x) STRINGIFY_DETAIL(x)
#define AT() " \tat file: " __FILE__ ":" STRINGIFY(__LINE__)

enum class VerifiableNonNullCheckerErrorKind : unsigned {
  NullableDereference,     // *GetNullable();
  NullptrPassedToNonnull,  // F(nullptr);
  NullablePassedToNonnull, // F(GetNullable());

  kCount
};

bool isPointerType(const QualType &T) { return T->getAs<PointerType>(); }

bool isNonNullableType(const PointerType *T) {
  return T->hasAttr(attr::VerifiableNonNull);
}

class NullabilityState final {
public:
  explicit NullabilityState(const bool isNonnull,
                            std::optional<const Expr *> source = std::nullopt)
      : mIsNonnull(isNonnull), mSource(std::move(source)) {}
  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddBoolean(mIsNonnull);
    ID.AddPointer(mSource.value_or(nullptr));
  }
  auto IsNonnull() const { return mIsNonnull; }
  auto Source() const { return mSource; }

private:
  bool mIsNonnull;
  std::optional<const Expr *> mSource;
};

bool operator==(const NullabilityState &Lhs, const NullabilityState &Rhs) {
  return Lhs.IsNonnull() == Rhs.IsNonnull() && Lhs.Source() == Rhs.Source();
}
} // namespace

REGISTER_MAP_WITH_PROGRAMSTATE(NullabilityMap, const MemRegion *,
                               NullabilityState)

namespace {
class VerifiableNonNullChecker final
    : public Checker<check::PreCall, check::PreStmt<ReturnStmt>,
                     check::PostStmt<ExplicitCastExpr>> {
public:
  [[maybe_unused]] void checkPreCall(const CallEvent &Call,
                                     CheckerContext &C) const;
  [[maybe_unused]] void checkPreStmt(const ReturnStmt *S,
                                     CheckerContext &C) const;
  [[maybe_unused]] void checkPostStmt(const ExplicitCastExpr *CE,
                                      CheckerContext &C) const;

  void registerChecker(VerifiableNonNullCheckerErrorKind Kind,
                       CheckerNameRef CN);

private:
  void reportBug(StringRef Msg, VerifiableNonNullCheckerErrorKind Kind,
                 CheckerContext &C, ExplodedNode *N, const Expr *E) const;

  [[nodiscard]] const std::unique_ptr<BugType> &
  getBugType(VerifiableNonNullCheckerErrorKind Kind) const;

  [[nodiscard]] const SymbolicRegion *getTrackingRegion(const SVal &V) const;

  CheckerNameRef
      CNs[static_cast<unsigned>(VerifiableNonNullCheckerErrorKind::kCount)];
  mutable std::unique_ptr<BugType>
      BTs[static_cast<unsigned>(VerifiableNonNullCheckerErrorKind::kCount)];
};

void VerifiableNonNullChecker::registerChecker(
    const VerifiableNonNullCheckerErrorKind Kind, const CheckerNameRef CN) {
  CNs[static_cast<unsigned>(Kind)] = CN;
}

[[nodiscard]] const std::unique_ptr<BugType> &
VerifiableNonNullChecker::getBugType(
    VerifiableNonNullCheckerErrorKind Kind) const {
  const unsigned I = static_cast<unsigned>(Kind);
  if (!BTs[I])
    BTs[I].reset(new BugType(CNs[I], "TODO", categories::MemoryError));
  return BTs[I];
}

const SymbolicRegion *
VerifiableNonNullChecker::getTrackingRegion(const SVal &V) const {
  auto &&SValAsRegion = V.getAs<loc::MemRegionVal>();
  if (!SValAsRegion)
    return nullptr;

  auto &&R = SValAsRegion->getRegion();

  return dyn_cast<SymbolicRegion>(R);
}

void VerifiableNonNullChecker::checkPreCall(const CallEvent &Call,
                                            CheckerContext &C) const {
  if (!Call.getDecl())
    return;

  llvm::dbgs() << __PRETTY_FUNCTION__ << '\n';
  Call.dump(llvm::dbgs());
  llvm::dbgs() << "\n\n";

  auto &&State = C.getState();

  unsigned I{};
  auto &&NArgs = Call.getNumArgs();
  for (const auto *Param : Call.parameters()) {
    if (!isPointerType(Param->getType()))
      continue;

    if (Param->isParameterPack()) { // TODO : ?? mb check param-pack
      llvm::dbgs() << "Param->isParameterPack()" << AT() << '\n';
      break;
    }

    if (I >= NArgs) {
      llvm::dbgs() << "I >= NArgs" << AT() << '\n';
      break;
    }

    const auto *ArgExpr = Call.getArgExpr(I);

    llvm::dbgs() << "ArgSVal = ";
    Call.getArgSVal(I).dump();
    llvm::dbgs() << '\n';

    llvm::dbgs() << "Call.getArgSVal(I).getAs<UndefinedVal>().has_value() = "
                 << Call.getArgSVal(I).getAs<UndefinedVal>().has_value()
                 << '\n';

    auto &&ArgSVal = Call.getArgSVal(I++).getAs<DefinedOrUnknownSVal>();
    if (!ArgSVal) {
      // TODO : warning if expression type not nonnull and no invariant
      llvm::dbgs() << "!ArgSVal" << AT() << '\n';
      continue;
    }

    auto &&SValIsNull = State->isNull(*ArgSVal);

    auto &&IsParamNonNullable = isNonNullableType(
        Param->getType()
            ->getAs<PointerType>()); // TODO : mb change to getOriginalType ?
    auto &&IsExprTypeNonNullable = isNonNullableType(
        ArgExpr->IgnoreImpCasts()
            ->getType()
            ->getAs<PointerType>()); // TODO : special check that ignore casts?

    llvm::dbgs() << "SValIsNull.isConstrainedTrue() && !IsExprTypeNonNullable "
                    "&& IsParamNonNullable"
                 << AT() << '\n';
    llvm::dbgs() << "SValIsNull.isConstrainedTrue() = "
                 << SValIsNull.isConstrainedTrue() << '\n';
    llvm::dbgs() << "IsExprTypeNonNullable = " << IsExprTypeNonNullable << '\n';
    llvm::dbgs() << "IsParamNonNullable = " << IsParamNonNullable << '\n';

    if (SValIsNull.isConstrainedTrue() // explicitly nullptr
        && !IsExprTypeNonNullable      // passed explicitly nullptr
        && IsParamNonNullable) {
      auto *N = C.generateErrorNode(State);
      if (!N)
        return;

      SmallString<256> Buf;
      llvm::raw_svector_ostream OS(Buf);
      auto &&PI = Param->getFunctionScopeIndex() + 1;
      OS << "nullptr passed to a callee that requires a non-null pointer as "
         << PI << llvm::getOrdinalSuffix(PI) << " parameter";

      reportBug(OS.str(),
                VerifiableNonNullCheckerErrorKind::NullptrPassedToNonnull, C, N,
                ArgExpr);

      return;
    }

    const MemRegion *R = getTrackingRegion(*ArgSVal);
    if (!R)
      continue;

    const NullabilityState *S = State->get<NullabilityMap>(R);

    // TODO : handle VerifiableNonNullCheckerErrorKind::NullablePassedToNonnull
  }
}

void VerifiableNonNullChecker::checkPreStmt(const ReturnStmt *S,
                                            CheckerContext &C) const {
  llvm::dbgs() << __PRETTY_FUNCTION__ << '\n';
  S->dump();
  llvm::dbgs() << "\n\n";

  auto &&RE = S->getRetValue();
  if (!RE) {
    llvm::dbgs() << "return without value" << '\n';
    return;
  }

  auto &&FuncDecl = C.getLocationContext()->getDecl()->getAsFunction();
  if (!FuncDecl) {
    llvm::dbgs() << "no function decl" << '\n';
    return;
  }

  auto &&RequiredReturnTypeQT = FuncDecl->getReturnType();
  if (!RequiredReturnTypeQT->isPointerType()) {
    llvm::dbgs() << "required return type is not pointer" << '\n';
    return;
  }

  auto &&RequiredReturnType = RequiredReturnTypeQT->getAs<PointerType>();

  auto &&IsRequiredReturnTypeNonNullable =
      isNonNullableType(RequiredReturnType);
  if (!RE->getType()->isPointerType())
    return;
  auto &&IsActualReturnExprTypeNonNullable = isNonNullableType(
      RE->IgnoreImpCasts()
          ->getType()
          ->getAs<PointerType>()); // TODO : special check that ignore casts?

  llvm::dbgs() << "IsRequiredReturnTypeNonNullable = "
               << IsRequiredReturnTypeNonNullable << '\n';
  llvm::dbgs() << "IsActualReturnExprTypeNonNullable = "
               << IsActualReturnExprTypeNonNullable << '\n';

  auto &&State = C.getState();

  auto &&ReturnSVal = C.getSVal(S).getAs<DefinedOrUnknownSVal>();
  if (!ReturnSVal)
    return; // TODO: no value to analysis / warn?

  auto &&ReturnSValIsNull = State->isNull(*ReturnSVal);
}

void VerifiableNonNullChecker::checkPostStmt(const ExplicitCastExpr *CE,
                                             CheckerContext &C) const {
  llvm::dbgs() << __PRETTY_FUNCTION__ << '\n';
  CE->dump();
  llvm::dbgs() << "\n\n";

  auto &&OT = CE->getSubExpr()->getType();
  auto &&CT = CE->getType();

  // TODO
}

void VerifiableNonNullChecker::reportBug(
    StringRef Msg, const VerifiableNonNullCheckerErrorKind Kind,
    CheckerContext &C, ExplodedNode *N, const Expr *E) const {
  auto &&BR = C.getBugReporter();

  auto &&BT = getBugType(Kind);
  auto &&R = std::make_unique<PathSensitiveBugReport>(*BT, Msg, N);
  BR.emitReport(std::move(R));
}

/* PreStmt<> PostStmt<>
 * PreCall PostCall
 * BeginFunction EndFunction
 *
 *
 */

} // namespace

#if 0
void ento::registerVerifiableNonNullDereferenceChecker(CheckerManager &mgr) {
  mgr.registerChecker<VerifiableNonNullDereferenceChecker>();
  VerifiableNonNullDereferenceChecker *C =
      mgr.getChecker<VerifiableNonNullDereferenceChecker>();
  C->CheckerName = mgr.getCurrentCheckerName();
}

bool ento::shouldRegisterVerifiableNonNullDereferenceChecker(
    CheckerManager const &) {
  return true;
}
#endif

// void ento::registerVerifiableNonNullDereferenceChecker(CheckerManager &mgr) {
//   mgr.registerChecker<VerifiableNonNullChecker>();
//   VerifiableNonNullChecker *C = mgr.getChecker<VerifiableNonNullChecker>();
//
//   // TODO : separate into different registers due to Checkers.td
//   registerChecker(
//       C, VerifiableNonNullCheckerErrorKind::NullptrPassedToNonnull,
//       mgr.getCurrentCheckerName() /* TODO : change to right checker anme */);
// }
//
// bool ento::shouldRegisterVerifiableNonNullDereferenceChecker(
//     CheckerManager const &) {
//   return true;
// }
//
// void ento::registerVerifiableNonNullParamChecker(CheckerManager &mgr) {
//   mgr.registerChecker<VerifiableNonNullParamChecker>();
//   // VerifiableNonNullDereferenceChecker *C =
//   //     mgr.getChecker<VerifiableNonNullDereferenceChecker>();
//   // C->CheckerName = mgr.getCurrentCheckerName();
// }
//
// bool ento::shouldRegisterVerifiableNonNullParamChecker(CheckerManager const
// &) {
//   return true;
// }

void ento::registerVerifiableNonNullChecker(CheckerManager &mgr) {
  mgr.registerChecker<VerifiableNonNullChecker>();
  // VerifiableNonNullChecker *C = mgr.getChecker<VerifiableNonNullChecker>();
  //
  // TODO : separate into different registers due to Checkers.td
  // registerChecker(
  //     C, VerifiableNonNullCheckerErrorKind::NullptrPassedToNonnull,
  //     mgr.getCurrentCheckerName() /* TODO : change to right checker anme */);
}

bool ento::shouldRegisterVerifiableNonNullChecker(CheckerManager const &) {
  return true;
}

#define REGISTER_VERIFIABLE_NONNULL_CHECKER(CHECKER_NAME)                      \
  void ento::register##CHECKER_NAME(CheckerManager &mgr) {                     \
    VerifiableNonNullChecker *C = mgr.getChecker<VerifiableNonNullChecker>();  \
    C->registerChecker(VerifiableNonNullCheckerErrorKind::CHECKER_NAME,        \
                       mgr.getCurrentCheckerName());                           \
  }                                                                            \
                                                                               \
  bool ento::shouldRegister##CHECKER_NAME(CheckerManager const &) {            \
    return true;                                                               \
  }

REGISTER_VERIFIABLE_NONNULL_CHECKER(NullableDereference)
REGISTER_VERIFIABLE_NONNULL_CHECKER(NullptrPassedToNonnull)
REGISTER_VERIFIABLE_NONNULL_CHECKER(NullablePassedToNonnull)
