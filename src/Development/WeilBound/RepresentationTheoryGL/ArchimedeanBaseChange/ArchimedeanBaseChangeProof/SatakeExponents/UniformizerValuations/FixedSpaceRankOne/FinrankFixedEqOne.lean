module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.Rg.BcB.F.EigA

section Sums

theorem out_mk_inv {H M : Type} [Group H] (A : Subgroup H) (F : H → M) (hF : ∀ x, ∀ a ∈ A, F (x * a) = F x)
    (y : H) : F ((y : H ⧸ A).out) = F y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A y
  rw [ha, hF _ _ a.2]

end Sums

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]


def GelPair (K : Subgroup G) : Prop :=
  (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) ∧
    ∃ τ : G → G, (∀ a b, τ (a * b) = τ b * τ a) ∧ (∀ a, τ (τ a) = a) ∧
      (∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) ∧ ∀ k ∈ K, τ k ∈ K

end PositivityTheory.Rg.BcB.F.EigA

end
