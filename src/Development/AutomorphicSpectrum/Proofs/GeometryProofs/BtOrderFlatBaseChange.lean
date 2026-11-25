module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValAtRestrict
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.FlatBC

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

def kapL (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    FractionRing R →ₗ[R] FractionRing R' where
  toFun := κ
  map_add' := map_add κ
  map_smul' r x := by
    have := congr($hκ r)
    simp only [RingHom.comp_apply] at this
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply, this,
      IsScalarTower.algebraMap_apply R R' (FractionRing R')]

end Alg

section Sch

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def secFn (Γ : QFGroup R T) : Submodule R (T → FractionRing R) where
  carrier := {f | ∃ s : Γ(Γ.G.left, ⊤), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤),
    valAt (Γ.pt t).left ⊤ h s = f t}
  add_mem' := by
    rintro f f' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_add, hs, hs']; rfl⟩
  zero_mem' := ⟨0, fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_zero]; rfl⟩
  smul_mem' := by
    rintro r f ⟨s, hs⟩
    refine ⟨(Γ.G.hom.appLE ⊤ ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * s,
      fun t h => ?_⟩
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_mul, PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_const, hs]
    simp [Algebra.smul_def]

lemma mem_btOrder_iff [Finite T] (Γ : QFGroup R T) (f : T → R) :
    f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ secFn Γ := by
  have hmem : f ∈ Γ.btOrder ⊤ ↔ f ∈ Γ.btSet ⊤ :=
    PositivityTheory.HtPt.Twhopf.mem_order R T Γ ⊤ f
  rw [hmem]
  refine forall_congr' fun t => ?_
  have := PositivityTheory.HtPt.Unc.reg_iff R T Γ ⊤ (fun h => algebraMap R (FractionRing R) (f (t * h)))
  exact this

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem val_mem_span [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (x : Γ(Γ'.G.left, ⊤)) :
    (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) x) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)} := by
  haveI := Γ.quasiCompact
  haveI := Γ.separated
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have H := hbc.cart
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _)
    (by simp)).1 (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (Γ.G.hom.isCompact_preimage (isAffineOpen_top _).isCompact)
      (Γ.G.hom.isQuasiSeparated_preimage (isAffineOpen_top _).isQuasiSeparated))
  refine PositivityTheory.HtPt.Htat.ValuationInjectivePi.pushout_induction po (fun y => (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) y) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)}) ?_ ?_ ?_ ?_ x
  · have : (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) (0 : Γ(Γ'.G.left, ⊤))) = 0 := by
      funext t; exact PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_zero _ _ _
    rw [this]
    exact Submodule.zero_mem _
  · intro s
    refine Submodule.subset_span ⟨fun t => valAt (Γ.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) s, ⟨s, fun _ _ => rfl⟩, ?_⟩
    funext t
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp (Γ'.pt t).left F ⊤ ⊤ _ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _),
      PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_congr (_root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hbc κ hκ t) _ _ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _),
      PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_map κ _ _ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _)]
  · intro c n hn
    have : (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) (((Γ'.G.hom.appLE ⊤ ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _)).hom c) * n)) =
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom c) •
          (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) n) := by
      funext t
      rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_mul, PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_const]
      simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ hn
  · intro p q hp hq
    have : (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) (p + q)) =
        (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) p) + (fun t => valAt (Γ'.pt t).left ⊤ (PositivityTheory.HtPt.Htat.ValuationInjectivePi.top_le_pre _) q) := by
      funext t
      exact PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_add _ _ _ _ _
    rw [this]
    exact Submodule.add_mem _ hp hq

end Sch

end GlobalTheory.CompanionTheory.Ar.BT.FlatBC
