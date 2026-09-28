import Jsp000216.CyclicDenseCoreFromBohr
import Jsp000216.GAPCoverReduction

namespace Jsp000216

noncomputable section

/-- Existentially package the explicit GAP-cover constants while they are still
variables.  The infinite argument needs only existence of uniform constants. -/
theorem exists_uniformGAPCoverF_of_denseCore {K R D : ℕ}
    (hK : 1 ≤ K) (hcore : DenseGAPCoreF K R D) :
    ∃ R' C' : ℕ, UniformGAPCoverF K R' C' := by
  exact ⟨R + K ^ 5 * D, 2 ^ (R + K ^ 5 * D) * K ^ 4,
    uniformGAPCoverF_of_denseCore hK hcore⟩

/-- Combine the cyclic-model reduction with the existential GAP-cover wrapper
before any large constants are specialized. -/
theorem exists_uniformGAPCoverF_of_cyclicDenseCore {K R D : ℕ}
    (hK : 1 ≤ K)
    (hcyc : UniformCyclicDenseCoreF (32 * K ^ 16) R D) :
    ∃ R' C' : ℕ, UniformGAPCoverF K R' C' := by
  exact exists_uniformGAPCoverF_of_denseCore hK
    (denseGAPCoreF_of_cyclicDenseCore hK hcyc)

/-- The structural input previously isolated as an assumption is now
unconditional: there exist fixed rank and box-cardinality constants such that
every finite integer set of doubling at most `12` is contained in a GAP with
those uniform bounds.

The explicit Bohr constants remain hidden behind generic existential theorems,
so specializing to the large Ruzsa-model density parameter never asks the
kernel to evaluate an astronomically large natural-number power. -/
theorem erdos245_exists_uniformGAPCoverF :
    ∃ R C : ℕ, UniformGAPCoverF 12 R C := by
  have hq : 1 ≤ 32 * 12 ^ 16 := by positivity
  obtain ⟨R, D, hcyc⟩ :=
    exists_uniformCyclicDenseCoreF_from_bohr (32 * 12 ^ 16) hq
  exact exists_uniformGAPCoverF_of_cyclicDenseCore
    (K := 12) (R := R) (D := D) (by omega) hcyc

end

end Jsp000216
