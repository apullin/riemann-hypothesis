module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB

structure Datum (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal


end PositivityTheory.Rg.BcB

end
