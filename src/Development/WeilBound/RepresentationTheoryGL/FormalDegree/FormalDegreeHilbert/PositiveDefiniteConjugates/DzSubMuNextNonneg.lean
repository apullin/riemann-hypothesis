module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := ReciprocityTheory.ChartRestriction.DS.S7.isHermitian_of_mem_noncompactPart' hX
  ext a b
  show (if h : b < a ∧ ε a ≠ ε b then X a b else if h' : a < b ∧ ε b ≠ ε a then star (X b a) else 0) = X a b
  split_ifs with h1 h2
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    simpa [Matrix.conjTranspose_apply] using h3
  · symm
    apply _root_.ReciprocityTheory.ChartRestriction.DS.inP_apply_eq_zero hX
    by_contra hne
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact h2 ⟨hlt, fun e => hne e.symm⟩
    · exact hne (by rw [heq])
    · exact h1 ⟨hgt, hne⟩

end PositivityTheory.RgFd
