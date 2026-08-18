import Jacobian

namespace JacobianConjecture

/-- The generalized Jacobian conjecture is false. -/
theorem jacobian_conjecture {k : Type} [CommRing k] [Nontrivial k] :
    False ↔ ∀ {σ : Type} [Fintype σ] [DecidableEq σ], JacobianConjectureProp k σ := by
  sorry

end JacobianConjecture
