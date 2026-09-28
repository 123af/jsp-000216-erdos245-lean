import Jsp000216.GAPBasic

open scoped Pointwise

namespace Jsp000216

/-- A quantitative Freiman-type covering statement at one fixed doubling
constant.  No theorem is assumed here: this is only the precise interface
needed by the infinite gap argument. -/
def UniformGAPCoverF (K R C : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    (A + A).card ≤ K * A.card →
      ∃ Q : GAPF,
        Q.rank ≤ R ∧
        A ⊆ Q.carrier ∧
        Q.boxCard ≤ C * A.card

end Jsp000216
