module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_perm_of_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → ((K → ℤ) → ℤ)) := by
    constructor
    intro a b g
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring
  unfold intNumL intNum GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

end GlobalTheory.CompanionTheory.Ar.Num
