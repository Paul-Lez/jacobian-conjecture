import Mathlib

namespace JacobianConjecture

section Prelims

variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}

variable (k σ τ) in
/-- The type of regular functions from $k^σ$ to $k^τ$. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- The Jacobian of a vector-valued polynomial function, viewed as a polynomial. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)

/-- The composition of two vector-valued polynomial functions. -/
noncomputable def comp
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun i => MvPolynomial.bind₁ F (G i)

variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

end RegularFunction

end Prelims

open RegularFunction

/-- The Jacobian conjecture for a coefficient ring and a finite variable index type. -/
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

namespace RegularFunction

variable {k : Type*} [CommRing k]

/-- Evaluate a regular function at a point with coordinates in a coefficient algebra. -/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t => MvPolynomial.aeval a (F t)

/-- Evaluation is compatible with composition of regular functions. -/
lemma comp_aeval
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  sorry

end RegularFunction

section Counterexample

open RegularFunction MvPolynomial

variable (k : Type*)

name_poly_vars X, Y, Z over k

/-- A determinant-one variant of the Alpöge--Fable polynomial counterexample. -/
noncomputable abbrev G [CommRing k] : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + 2 * X * Y) ^ 3 * Z + 4 * Y ^ 2 * (1 + 2 * X * Y) * (2 + 3 * (X * Y)),
    Y + 3 * X * (1 + 2 * X * Y) ^ 2 * Z + 12 * X * Y ^ 2 * (2 + 3 * (X * Y)),
    -X + 3 * X ^ 2 * Y + X ^ 3 * Z]

/-- The Jacobian determinant of `G` is one. -/
lemma det_jacobian_G [CommRing k] : (G k).Jacobian.det = 1 := by
  sorry

/-- `G` identifies the distinct points `(1, 0, 1)` and `(0, 3, -71)`. -/
lemma aeval_G_eq [CommRing k] :
    (G k).aeval ![1, 0, (1 : k)] = (G k).aeval ![0, 3, -71] := by
  sorry

/-- The generalized Jacobian conjecture is false. -/
theorem jacobian_conjecture {k : Type} [CommRing k] [Nontrivial k] :
    False ↔ ∀ {σ : Type} [Fintype σ] [DecidableEq σ], JacobianConjectureProp k σ := by
  sorry

end Counterexample

end JacobianConjecture
