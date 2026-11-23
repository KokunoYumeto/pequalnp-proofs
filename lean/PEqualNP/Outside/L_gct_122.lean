import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065

-- L-gct-122 (Lemma K): a complex linear space in C^M on which the power sums
-- x_1^2 + ... + x_M^2 and x_1^4 + ... + x_M^4 both vanish has dimension at most M/3.
-- Proof: polarize. Then V = W * W (span of coordinatewise products) is isotropic for the
-- dot product and orthogonal to the all-ones vector. If the stabilizer of V is the scalars,
-- Kneser for codes (L-gct-065) with S = T = W gives 2 dim W <= dim V + 1, and V + C1 inside
-- the orthogonal of V gives 2 dim V + 1 <= M, so 4 dim W <= M + 1, hence 3 dim W <= M.
-- Otherwise split the coordinates along an idempotent of the stabilizer and induct on M.
-- The helper layer follows the project file Gct/Helpers/FermatFromKneser.lean (the p3 case).

namespace LGct122K

open Module Finset

section General

variable {ι : Type}

-- The polarized hypotheses: W is isotropic for the dot product and for the
-- four-linear form sum u_i v_i z_i w_i.
def KIso [Fintype ι] (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∀ w ∈ W, ∑ i, u i * v i * z i * w i = 0)

-- The Kneser statement for codes indexed by ι.
def KneserFor (ι : Type) [Fintype ι] : Prop :=
  ∀ S T St : Submodule ℂ (ι → ℂ), S ≠ ⊥ → T ≠ ⊥ →
    (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ (S * T) + finrank ℂ St

-- The stabilizer of a subspace in the algebra ι → ℂ.
def stab (V : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {x | ∀ v ∈ V, x * v ∈ V}
  add_mem' {a b} ha hb v hv := by rw [add_mul]; exact V.add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := by rw [zero_mul]; exact V.zero_mem
  smul_mem' c x hx v hv := by rw [smul_mul_assoc]; exact V.smul_mem c (hx v hv)

theorem one_mem_stab (V : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ stab V := fun v hv => by
  rwa [one_mul]

theorem mul_mem_stab {V : Submodule ℂ (ι → ℂ)} {x y : ι → ℂ} (hx : x ∈ stab V)
    (hy : y ∈ stab V) : x * y ∈ stab V := fun v hv => by
  rw [mul_assoc]; exact hx _ (hy v hv)

-- The dot product as a linear map to the dual.
noncomputable def dotDual [Fintype ι] : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by ring)

theorem dotDual_apply [Fintype ι] (v z : ι → ℂ) : dotDual v z = ∑ i, v i * z i := rfl

theorem dotDual_injective [Fintype ι] : Function.Injective (dotDual (ι := ι)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have h := LinearMap.congr_fun hv (Pi.single j 1)
  rw [dotDual_apply] at h
  simpa [Pi.single_apply] using h

-- A subspace orthogonal to W has dimension at most |ι| - dim W.
theorem perp_bound [Fintype ι] (V W : Submodule ℂ (ι → ℂ))
    (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    finrank ℂ V + finrank ℂ W ≤ Fintype.card ι := by
  have hle : V.map dotDual ≤ W.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : finrank ℂ (V.map dotDual) = finrank ℂ V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ dotDual_injective V)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  omega

-- Lagrange interpolation in the stabilizer: a level set indicator of an element.
theorem exists_indicator [Fintype ι] {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ stab V)
    (i : ι) : ∃ e ∈ stab V, ∀ k, e k = if x k = x i then 1 else 0 := by
  classical
  refine ⟨∏ c ∈ (univ.image x).erase (x i), (x i - c)⁻¹ • (x - c • 1), ?_, ?_⟩
  · refine Finset.prod_induction _ (· ∈ stab V) (fun a b ha hb => mul_mem_stab ha hb)
      (one_mem_stab V) fun c _ => ?_
    exact (stab V).smul_mem _ ((stab V).sub_mem hx ((stab V).smul_mem _ (one_mem_stab V)))
  · intro k
    rw [Finset.prod_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    split_ifs with hk
    · refine Finset.prod_eq_one fun c hc => ?_
      have hc' : c ≠ x i := (Finset.mem_erase.1 hc).1
      rw [hk]
      exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hc'))
    · refine Finset.prod_eq_zero (i := x k) ?_ (by rw [sub_self, mul_zero])
      exact Finset.mem_erase.2 ⟨hk, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

-- Restriction of a vector to the coordinates where p is one.
noncomputable def restr (p : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ({k // p k = 1} → ℂ) :=
  LinearMap.funLeft ℂ ℂ Subtype.val

theorem restr_apply (p u : ι → ℂ) (k : {k // p k = 1}) : restr p u k = u k := rfl

theorem sum_restr [Fintype ι] (p : ι → ℂ) (hp : ∀ k, p k = 0 ∨ p k = 1) (f : ι → ℂ) :
    ∑ k : {k // p k = 1}, f k = ∑ k, p k * f k := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => p k = 1) (fun k => p k * f k)]
  have h2 : ∑ k : {k // ¬ p k = 1}, p k * f k = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hp k with h | h
    · rw [h, zero_mul]
    · exact absurd h k.2
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [k.2, one_mul]

-- Every element of W * W sums to zero, and W * W is isotropic for the dot product.
theorem sum_zero_of_mem [Fintype ι] {W : Submodule ℂ (ι → ℂ)} (hW : KIso W) :
    ∀ a ∈ W * W, ∑ i, a i = 0 := by
  intro a ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro u hu v hv
    simpa only [Pi.mul_apply] using hW.1 u hu v hv
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

theorem iso_of_mem [Fintype ι] {W : Submodule ℂ (ι → ℂ)} (hW : KIso W) :
    ∀ a ∈ W * W, ∀ b ∈ W * W, ∑ i, a i * b i = 0 := by
  intro a ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro u hu v hv b hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro z hz w hw
      have := hW.2 u hu v hv z hz w hw
      simpa only [Pi.mul_apply, mul_assoc] using this
    · intro c d hc hd
      simp only [Pi.add_apply, mul_add, sum_add_distrib, hc, hd, add_zero]
  · intro a b ha hb c hc
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha c hc, hb c hc, add_zero]

-- The restriction of W along a 0/1 element of the stabilizer of W * W is again isotropic.
theorem restr_iso [Fintype ι] {W : Submodule ℂ (ι → ℂ)} (hW : KIso W) {p : ι → ℂ}
    (hp : p ∈ stab (W * W)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    KIso (W.map (restr p)) := by
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have := sum_zero_of_mem hW _ (hp _ (Submodule.mul_mem_mul hu hv))
    simpa only [Pi.mul_apply] using this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * z k * w k)]
    have := iso_of_mem hW _ (hp _ (Submodule.mul_mem_mul hu hv)) _ (Submodule.mul_mem_mul hz hw)
    simpa only [Pi.mul_apply, mul_assoc] using this

-- Splitting the coordinates in two: dim W <= dim W_B + dim W_B'.
theorem finrank_split [Fintype ι] (W : Submodule ℂ (ι → ℂ)) (e f : ι → ℂ)
    (hef : ∀ k, e k = 1 ∨ f k = 1) :
    finrank ℂ W ≤ finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f)) := by
  let R := (restr e).prod (restr f)
  have hR : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    rcases hef k with h | h
    · have := congr_fun (congr_arg Prod.fst hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
    · have := congr_fun (congr_arg Prod.snd hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
  have e1 : finrank ℂ (W.map R) = finrank ℂ W :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hR W)).symm
  let A := {k // e k = 1} → ℂ
  let B := {k // f k = 1} → ℂ
  have hle : W.map R ≤ (W.map (restr e)).map (LinearMap.inl ℂ A B) ⊔
      (W.map (restr f)).map (LinearMap.inr ℂ A B) := by
    rintro _ ⟨u, hu, rfl⟩
    have : R u = LinearMap.inl ℂ A B (restr e u) + LinearMap.inr ℂ A B (restr f u) := by
      simp [R]
    rw [this]
    exact Submodule.add_mem_sup ⟨_, ⟨u, hu, rfl⟩, rfl⟩ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((W.map (restr e)).map (LinearMap.inl ℂ A B)) ((W.map (restr f)).map (LinearMap.inr ℂ A B))
  have h3 := Submodule.finrank_map_le (LinearMap.inl ℂ A B) (W.map (restr e))
  have h4 := Submodule.finrank_map_le (LinearMap.inr ℂ A B) (W.map (restr f))
  rw [← e1]
  exact h1.trans (h2.trans (add_le_add h3 h4))

end General

-- Transport of the Kneser statement from Fin n to any finite index type.
theorem kneserFor_of_fin
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St)
    (ι : Type) [Fintype ι] : KneserFor ι := by
  intro S T St hS hT hSt
  let Φ : (ι → ℂ) ≃ₐ[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Fintype.equivFin ι)
  have hfr : ∀ X : Submodule ℂ (ι → ℂ),
      finrank ℂ (X.map Φ.toLinearMap) = finrank ℂ X := fun X =>
    LinearEquiv.finrank_map_eq Φ.toLinearEquiv X
  have hne : ∀ X : Submodule ℂ (ι → ℂ), X ≠ ⊥ → X.map Φ.toLinearMap ≠ ⊥ := by
    intro X hX h
    apply hX
    rw [← Submodule.finrank_eq_zero, ← hfr X, h, finrank_bot]
  have hmul := Submodule.map_mul S T Φ.toAlgHom
  have key := hK _ (S.map Φ.toLinearMap) (T.map Φ.toLinearMap) (St.map Φ.toLinearMap)
    (hne S hS) (hne T hT) ?_
  · rw [hfr, hfr, hfr] at key
    erw [← hmul, hfr] at key
    exact key
  · intro x
    have hmul' : (S * T).map Φ.toLinearMap =
        S.map Φ.toLinearMap * T.map Φ.toLinearMap := hmul
    rw [← hmul']
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
      refine ⟨y * w, (hSt y).1 hy w hw, ?_⟩
      simp
    · intro h
      refine ⟨Φ.symm x, (hSt _).2 fun w hw => ?_, by simp⟩
      obtain ⟨w', hw', he⟩ := h (Φ w) ⟨w, hw, rfl⟩
      have : w' = Φ.symm x * w := by
        apply Φ.injective
        simp only [AlgEquiv.toLinearMap_apply] at he
        rw [he, map_mul, AlgEquiv.apply_symm_apply]
      rw [← this]
      exact hw'

-- The bound for polarized hypotheses on any finite index type, given Kneser.
theorem lemmaK_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), KIso W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  set V := W * W with hVdef
  have hone : (1 : ι → ℂ) ∉ V := by
    intro h
    have := iso_of_mem hW 1 h 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  · -- the stabilizer is the scalars: Kneser with S = T = W, and V + C1 orthogonal to V
    have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hU : finrank ℂ ↥(V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ V + 1 := by
      have hinf : V ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxV, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := V.smul_mem c⁻¹ hxV
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hk := hK ι W W (stab V) hW0 hW0 (fun x => Iff.rfl)
    have hperp : ∀ v ∈ V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}, ∀ z ∈ V, ∑ i, v i * z i = 0 := by
      intro v hv z hz
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 := iso_of_mem hW y hy z hz
      have h2 := sum_zero_of_mem hW z hz
      calc ∑ i, (y + c • 1) i * z i
          = ∑ i, y i * z i + c * ∑ i, z i := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ => ?_
            simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
            ring
        _ = 0 := by rw [h1, h2, mul_zero, add_zero]
    have hp := perp_bound (V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) V hperp
    have hWpos : 1 ≤ finrank ℂ W := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact hW0
    change _ + _ ≤ finrank ℂ V + _ at hk
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab V := (stab V).sub_mem (one_mem_stab V) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_iso hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_iso hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

theorem lemmaK_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) →
      (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
  intro m W h2 h4
  have hQ : ∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (W.add_mem hu hv), h2 u hu, h2 v hv, ← mul_sum] at key
    simpa using key
  have hF : ∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∀ w ∈ W, ∑ i, u i * v i * z i * w i = 0 := by
    intro u hu v hv z hz w hw
    have key : ∑ i, (24 : ℂ) * (u i * v i * z i * w i) =
        (∑ i, (u + v + z + w) i ^ 4)
          - (∑ i, (u + v + z) i ^ 4) - (∑ i, (u + v + w) i ^ 4)
          - (∑ i, (u + z + w) i ^ 4) - (∑ i, (v + z + w) i ^ 4)
          + (∑ i, (u + v) i ^ 4) + (∑ i, (u + z) i ^ 4) + (∑ i, (u + w) i ^ 4)
          + (∑ i, (v + z) i ^ 4) + (∑ i, (v + w) i ^ 4) + (∑ i, (z + w) i ^ 4)
          - (∑ i, u i ^ 4) - (∑ i, v i ^ 4) - (∑ i, z i ^ 4) - (∑ i, w i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h4 _ (W.add_mem (W.add_mem (W.add_mem hu hv) hz) hw),
      h4 _ (W.add_mem (W.add_mem hu hv) hz), h4 _ (W.add_mem (W.add_mem hu hv) hw),
      h4 _ (W.add_mem (W.add_mem hu hz) hw), h4 _ (W.add_mem (W.add_mem hv hz) hw),
      h4 _ (W.add_mem hu hv), h4 _ (W.add_mem hu hz), h4 _ (W.add_mem hu hw),
      h4 _ (W.add_mem hv hz), h4 _ (W.add_mem hv hw), h4 _ (W.add_mem hz hw),
      h4 u hu, h4 v hv, h4 z hz, h4 w hw, ← mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact lemmaK_general (kneserFor_of_fin hK) m (Fin m) (Fintype.card_fin m) W ⟨hQ, hF⟩

end LGct122K

theorem PEqualNP.Outside.L_gct_122 :
    ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) →
      (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m :=
  LGct122K.lemmaK_of_kneser PEqualNP.Gct.L065
