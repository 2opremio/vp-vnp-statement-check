import Independent
import Solution

/-!
# The proven statements imply the independent formalization

Translation lemmas between `Statement` (proven in `Solution`) and `Independent`, and the five
claims of `Independent` derived from the corresponding `Solution` theorems.
-/

open MvPolynomial
open scoped RatFunc

noncomputable section

namespace Bridge

universe u

/-! ## Circuits -/

section Circuits

variable {R : Type*} {σ : Type} [CommSemiring R]

theorem values_snoc_castSucc {k : ℕ} (Γ : Independent.Circuit R σ k) (g : Independent.Gate R σ k)
    (j : Fin k) : (Γ.snoc g).values j.castSucc = Γ.values j := by
  simp [Independent.Circuit.values]

theorem values_snoc_last {k : ℕ} (Γ : Independent.Circuit R σ k) (g : Independent.Gate R σ k) :
    (Γ.snoc g).values (Fin.last k) = g.eval Γ.values := by
  simp [Independent.Circuit.values]

/-- Every gate value is a variable, a constant, or a sum or product of two earlier values. -/
theorem values_cases {k : ℕ} (Γ : Independent.Circuit R σ k) (j : Fin k) :
    (∃ x, Γ.values j = X x) ∨ (∃ c, Γ.values j = C c) ∨
      (∃ a b : Fin k, a < j ∧ b < j ∧ Γ.values j = Γ.values a + Γ.values b) ∨
      (∃ a b : Fin k, a < j ∧ b < j ∧ Γ.values j = Γ.values a * Γ.values b) := by
  induction Γ with
  | nil => exact j.elim0
  | snoc Γ g ih =>
    induction j using Fin.lastCases with
    | last =>
      rw [values_snoc_last]
      cases g with
      | input x => exact Or.inl ⟨x, rfl⟩
      | const c => exact Or.inr (Or.inl ⟨c, rfl⟩)
      | add a b =>
        exact Or.inr (Or.inr (Or.inl ⟨a.castSucc, b.castSucc, Fin.castSucc_lt_last a,
          Fin.castSucc_lt_last b, by rw [values_snoc_castSucc, values_snoc_castSucc]; rfl⟩))
      | mul a b =>
        exact Or.inr (Or.inr (Or.inr ⟨a.castSucc, b.castSucc, Fin.castSucc_lt_last a,
          Fin.castSucc_lt_last b, by rw [values_snoc_castSucc, values_snoc_castSucc]; rfl⟩))
    | cast j =>
      rw [values_snoc_castSucc]
      rcases ih j with h | h | ⟨a, b, ha, hb, h⟩ | ⟨a, b, ha, hb, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨a.castSucc, b.castSucc, Fin.castSucc_lt_castSucc_iff.2 ha,
          Fin.castSucc_lt_castSucc_iff.2 hb, by simp only [values_snoc_castSucc, h]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a.castSucc, b.castSucc, Fin.castSucc_lt_castSucc_iff.2 ha,
          Fin.castSucc_lt_castSucc_iff.2 hb, by simp only [values_snoc_castSucc, h]⟩))

/-- An `Independent` circuit with `k` gates gives a `Statement` circuit with `k` gates. -/
theorem computes_of_circuit {k : ℕ} (Γ : Independent.Circuit R σ k) {f : MvPolynomial σ R}
    (hf : Γ.Computes f) : Statement.Computes f k := by
  obtain ⟨i, rfl⟩ := hf
  refine ⟨fun j => if h : j < k then Γ.values ⟨j, h⟩ else 0, fun j hj => ?_, i, i.isLt, by simp⟩
  simp only [dif_pos hj]
  rcases values_cases Γ ⟨j, hj⟩ with h | h | ⟨a, b, ha, hb, h⟩ | ⟨a, b, ha, hb, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, by simp [h]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, by simp [h]⟩))

/-- A `Statement` circuit with `s` gates gives an `Independent` circuit with `s` gates. -/
theorem circuit_of_computes {f : MvPolynomial σ R} {s : ℕ} (h : Statement.Computes f s) :
    ∃ Γ : Independent.Circuit R σ s, Γ.Computes f := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  have key : ∀ j ≤ s, ∃ Γ : Independent.Circuit R σ j, ∀ i : Fin j, Γ.values i = l i := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨.nil, fun i => i.elim0⟩
    | succ j ih =>
      intro hj
      obtain ⟨Γ, hΓ⟩ := ih (Nat.le_of_succ_le hj)
      have gate : ∃ g : Independent.Gate R σ j, g.eval Γ.values = l j := by
        rcases hl j hj with ⟨x, h⟩ | ⟨c, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩
        · exact ⟨.input x, h.symm⟩
        · exact ⟨.const c, h.symm⟩
        · exact ⟨.add ⟨a, ha⟩ ⟨b, hb⟩, by simp [Independent.Gate.eval, hΓ, h]⟩
        · exact ⟨.mul ⟨a, ha⟩ ⟨b, hb⟩, by simp [Independent.Gate.eval, hΓ, h]⟩
      obtain ⟨g, hg⟩ := gate
      refine ⟨Γ.snoc g, fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => rw [values_snoc_last, hg, Fin.val_last]
      | cast i => rw [values_snoc_castSucc, hΓ, Fin.val_castSucc]
  obtain ⟨Γ, hΓ⟩ := key s le_rfl
  exact ⟨Γ, ⟨k, hk⟩, hΓ _⟩

end Circuits

section Computes

variable {R S : Type*} {V W : Type} [CommSemiring R] [CommSemiring S]

/-- `Statement.Computes` is preserved by a ring hom sending variables to variables and
constants to constants. -/
theorem computes_hom (Ψ : MvPolynomial V R →+* MvPolynomial W S)
    (hX : ∀ x, ∃ w, Ψ (X x) = X w) (hC : ∀ c, ∃ b, Ψ (C c) = C b)
    {f : MvPolynomial V R} {s : ℕ} (h : Statement.Computes f s) : Statement.Computes (Ψ f) s := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  refine ⟨fun j => Ψ (l j), fun j hj => ?_, k, hk, rfl⟩
  rcases hl j hj with ⟨x, h⟩ | ⟨c, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩
  · obtain ⟨w, hw⟩ := hX x
    exact Or.inl ⟨w, by simp only [h, hw]⟩
  · obtain ⟨d, hd⟩ := hC c
    exact Or.inr (Or.inl ⟨d, by simp only [h, hd]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, by simp only [h, map_add]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, by simp only [h, map_mul]⟩))

theorem computes_rename (e : V → W) {f : MvPolynomial V R} {s : ℕ}
    (h : Statement.Computes f s) : Statement.Computes (rename e f) s :=
  computes_hom (rename e).toRingHom (fun x => ⟨e x, by simp⟩) (fun c => ⟨c, by simp⟩) h

theorem computes_map (φ : R →+* S) {f : MvPolynomial V R} {s : ℕ}
    (h : Statement.Computes f s) : Statement.Computes (map φ f) s :=
  computes_hom (map φ) (fun x => ⟨x, by simp⟩) (fun c => ⟨φ c, by simp⟩) h

theorem computes_mono {f : MvPolynomial V R} {s t : ℕ} (h : Statement.Computes f s)
    (hst : s ≤ t) : Statement.Computes f t := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  refine ⟨fun j => if j < s then l j else 0, fun j hj => ?_, k, hk.trans_le hst, by simp [hk]⟩
  by_cases hjs : j < s
  · simp only [if_pos hjs]
    rcases hl j hjs with h | h | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, by simp [ha.trans hjs, hb.trans hjs, h]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, by simp [ha.trans hjs, hb.trans hjs, h]⟩))
  · exact Or.inr (Or.inl ⟨0, by simp [hjs]⟩)

end Computes

theorem rename_symm_rename {R : Type*} [CommSemiring R] {V W : Type*} (e : V ≃ W)
    (p : MvPolynomial V R) : rename e.symm (rename e p) = p := by
  rw [rename_rename]
  convert rename_id_apply p
  funext x
  simp

/-! ## Border circuits: `RatFunc F` to `LaurentSeries F` -/

section Border

variable {F : Type u} [Field F]

theorem coe_ratFunc_poly (p : Polynomial F) :
    algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) p) =
      HahnSeries.ofPowerSeries ℤ F p := by
  rw [RatFunc.coe_coe]; rfl

theorem coeff_approx (c : F) (p : Polynomial F) {i : ℤ} (hi : i ≤ 0) :
    (algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F (RatFunc F) c) +
      algebraMap (RatFunc F) (LaurentSeries F) RatFunc.X *
        algebraMap (RatFunc F) (LaurentSeries F) (algebraMap (Polynomial F) (RatFunc F) p)).coeff i =
      if i = 0 then c else 0 := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), coe_ratFunc_poly,
    coe_ratFunc_poly, RatFunc.coe_X, HahnSeries.coeff_add, HahnSeries.coeff_single_mul,
    PowerSeries.coeff_coe, PowerSeries.coeff_coe, if_pos (by omega : i - 1 < 0)]
  rcases hi.lt_or_eq with h | rfl
  · simp [h, h.ne]
  · simp

/-- An `Independent` border circuit with `k` gates (over `F(ε)`, variables renamed along `e`)
gives a `Statement` approximating circuit with `k` gates (over `F((ε))`). -/
theorem approximates_of_circuit {σ V : Type} (e : σ ≃ V) {k : ℕ}
    (Γ : Independent.Circuit (RatFunc F) σ k) {f : MvPolynomial σ F} (h : Γ.Approximates f) :
    Statement.Approximates (rename e f) k := by
  obtain ⟨g, hg⟩ := h
  have hc := computes_rename e
    (computes_map (algebraMap (RatFunc F) (LaurentSeries F)) (computes_of_circuit Γ hg))
  refine ⟨_, hc, fun d i hi => ?_⟩
  simp only [map_add, map_mul, map_C, map_map, ← map_rename, rename_C, coeff_add, coeff_C_mul,
    coeff_map, RingHom.coe_comp, Function.comp_apply]
  exact coeff_approx _ _ hi

theorem approximates_mono {V : Type} {f : MvPolynomial V F} {s t : ℕ}
    (h : Statement.Approximates f s) (hst : s ≤ t) : Statement.Approximates f t := by
  obtain ⟨q, hq, hcoeff⟩ := h
  exact ⟨q, computes_mono hq hst, hcoeff⟩

end Border

/-! ## The polynomials -/

theorem permanent_eq (F : Type u) [CommSemiring F] (m : ℕ) :
    Independent.permanent F m = Statement.perm F m := by
  unfold Independent.permanent Statement.perm
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun π => ?_
  exact Fintype.prod_equiv π _ _ fun j => by simp

theorem isCycleOn_univ_iff {m : ℕ} (hm : 2 ≤ m) (π : Equiv.Perm (Fin m)) :
    π.IsCycleOn Set.univ ↔ π.IsCycle ∧ π.support = Finset.univ := by
  have hnt : (Set.univ : Set (Fin m)).Nontrivial :=
    ⟨⟨0, by omega⟩, trivial, ⟨1, by omega⟩, trivial, by simp [Fin.ext_iff]⟩
  constructor
  · intro h
    have hsupp : π.support = Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support, h.apply_ne hnt (Set.mem_univ x)]
    exact ⟨Equiv.Perm.isCycle_iff_exists_isCycleOn.2 ⟨Set.univ, hnt, h, fun x _ => Set.mem_univ x⟩,
      hsupp⟩
  · rintro ⟨h1, h2⟩
    convert h1.isCycleOn
    ext x
    simp only [Set.mem_univ, Set.mem_ofPred_eq, true_iff]
    rw [← Equiv.Perm.mem_support, h2]
    exact Finset.mem_univ x

/-- The two Hamiltonian cycle polynomials agree for `m ≥ 2` (for `m ≤ 1` the identity is a
cycle on `univ` but not `IsCycle`). -/
theorem hamCycle_eq (F : Type u) [CommSemiring F] {m : ℕ} (hm : 2 ≤ m) :
    Independent.hamCycle F m = Statement.hc F m := by
  classical
  unfold Independent.hamCycle Statement.hc
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext π
  simp [isCycleOn_univ_iff hm]

/-! ## Polynomial bounds -/

theorem polyBounded_of_le {t : ℕ → ℕ} (a : ℕ) (h : ∀ n, t n ≤ n ^ a + a) :
    Independent.PolyBounded t :=
  ⟨Polynomial.X ^ a + Polynomial.C a, fun n => by simpa using h n⟩

theorem polyBounded_max {t₁ t₂ : ℕ → ℕ} (h₁ : Independent.PolyBounded t₁)
    (h₂ : Independent.PolyBounded t₂) : Independent.PolyBounded fun n => max (t₁ n) (t₂ n) := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p + q, fun n => by
    simp only [Polynomial.eval_add]
    exact max_le ((hp n).trans (Nat.le_add_right _ _)) ((hq n).trans (Nat.le_add_left _ _))⟩

theorem exists_pow_bound {t : ℕ → ℕ} (h : Independent.PolyBounded t) :
    ∃ a, ∀ n, t n ≤ n ^ a + a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.eval 1 + p.natDegree, fun n => (hp n).trans ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : p.eval 0 ≤ p.eval 1 := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
      exact Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.zero_le 1) i)
    exact this.trans (le_add_left (Nat.le_add_right _ _))
  · have h1 : p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [one_pow, mul_one]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      simp only [one_pow, mul_one] at h1 ⊢
      omega
    · have h2 : p.eval 1 ≤ n ^ p.eval 1 :=
        (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn2 _)
      calc p.eval n ≤ p.eval 1 * n ^ p.natDegree := h1
        _ ≤ n ^ p.eval 1 * n ^ p.natDegree := Nat.mul_le_mul_right _ h2
        _ = n ^ (p.eval 1 + p.natDegree) := (pow_add _ _ _).symm
        _ ≤ _ := Nat.le_add_right _ _

/-! ## Families -/

/-- A `Statement` family as an `Independent` family, numbering the variables. -/
def toIndep {F : Type u} [CommSemiring F] (f : Statement.Family F) : Independent.PolyFamily F where
  nvars n := Fintype.card (f.vars n)
  poly n := rename (Fintype.equivFin (f.vars n)) (f.poly n)

theorem totalDegree_toIndep_le {F : Type u} [CommSemiring F] (f : Statement.Family F) (n : ℕ) :
    ((toIndep f).poly n).totalDegree ≤ (f.poly n).totalDegree :=
  totalDegree_rename_le _ _

theorem totalDegree_le_toIndep {F : Type u} [CommSemiring F] (f : Statement.Family F) (n : ℕ) :
    (f.poly n).totalDegree ≤ ((toIndep f).poly n).totalDegree := by
  conv_lhs => rw [← rename_symm_rename (Fintype.equivFin (f.vars n)) (f.poly n)]
  exact totalDegree_rename_le _ _

/-- Bounds of an `Independent` p-family with a size function `s`, as one `n ^ a + a`. -/
theorem exists_common_bound {F : Type u} [CommSemiring F] {f : Statement.Family F}
    (hf : Independent.IsPFamily (toIndep f)) {s : ℕ → ℕ} (hs : Independent.PolyBounded s) :
    ∃ a, ∀ n, Fintype.card (f.vars n) ≤ n ^ a + a ∧ (f.poly n).totalDegree ≤ n ^ a + a ∧
      s n ≤ n ^ a + a := by
  obtain ⟨a, ha⟩ := exists_pow_bound (polyBounded_max (polyBounded_max hf.1 hf.2) hs)
  refine ⟨a, fun n => ⟨?_, ?_, ?_⟩⟩
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans (ha n))
  · exact (totalDegree_le_toIndep f n).trans
      ((le_max_right _ _).trans ((le_max_left _ _).trans (ha n)))
  · exact (le_max_right _ _).trans (ha n)

theorem mem_VP_of_toIndep {F : Type u} [Field F] {f : Statement.Family F}
    (h : toIndep f ∈ Independent.VP F) : f ∈ Statement.VP F := by
  obtain ⟨hp, s, hs, hc⟩ := h
  obtain ⟨a, ha⟩ := exists_common_bound hp hs
  refine ⟨a, fun n => ⟨(ha n).1, (ha n).2.1, ?_⟩⟩
  obtain ⟨k, hk, Γ, hΓ⟩ := hc n
  have := computes_rename (Fintype.equivFin (f.vars n)).symm (computes_of_circuit Γ hΓ)
  dsimp only [toIndep] at this
  rw [rename_symm_rename] at this
  exact computes_mono this (hk.trans (ha n).2.2)

theorem mem_VPBar_of_toIndep {F : Type u} [Field F] {f : Statement.Family F}
    (h : toIndep f ∈ Independent.VPbar F) : f ∈ Statement.VPBar F := by
  obtain ⟨hp, s, hs, hc⟩ := h
  obtain ⟨a, ha⟩ := exists_common_bound hp hs
  refine ⟨a, fun n => ⟨(ha n).1, (ha n).2.1, ?_⟩⟩
  obtain ⟨k, hk, Γ, hΓ⟩ := hc n
  have := approximates_of_circuit (Fintype.equivFin (f.vars n)).symm Γ hΓ
  dsimp only [toIndep] at this
  rw [rename_symm_rename] at this
  exact approximates_mono this (hk.trans (ha n).2.2)

/-- Boolean sum, `Statement` form (extra bits as a `Fin r` summand) against `Independent` form
(extra bits as the last variables). -/
theorem booleanSum_eq {F : Type u} [Field F] {V : Type} {v : ℕ} (eF : V ≃ Fin v) (r : ℕ)
    (g : MvPolynomial (V ⊕ Fin r) F) :
    rename eF (∑ e : Fin r → Bool, aeval (Sum.elim X fun i => if e i then 1 else 0) g) =
      Independent.booleanSum v (v + r)
        (rename ((Equiv.sumCongr eF (Equiv.refl _)).trans finSumFinEquiv) g) := by
  have hr : v + r - v = r := by omega
  rw [map_sum, Independent.booleanSum]
  refine Fintype.sum_equiv (Equiv.arrowCongr (finCongr hr.symm) (Equiv.refl Bool)) _ _
    fun e => ?_
  rw [bind₁_rename, aeval_eq_bind₁, rename_bind₁]
  congr 1
  congr 1
  funext x
  rcases x with x | i
  · simp [Independent.booleanSubst]
  · have hi : ¬ (v + (i : ℕ) < v) := by omega
    cases he : e i <;> simp [Independent.booleanSubst, hi, he]

theorem toIndep_mem_VNP {F : Type u} [Field F] {f : Statement.Family F}
    (h : f ∈ Statement.VNP F) : toIndep f ∈ Independent.VNP F := by
  obtain ⟨r, g, ⟨a, ha⟩, hfg⟩ := h
  let eG : ∀ n, f.vars n ⊕ Fin (r n) ≃ Fin (Fintype.card (f.vars n) + r n) := fun n =>
    (Equiv.sumCongr (Fintype.equivFin (f.vars n)) (Equiv.refl _)).trans finSumFinEquiv
  let G : Independent.PolyFamily F :=
    ⟨fun n => Fintype.card (f.vars n) + r n, fun n => rename (eG n) (g n)⟩
  have hcard : ∀ n, Fintype.card (f.vars n) + r n ≤ n ^ a + a := fun n => by
    simpa [Fintype.card_sum] using (ha n).1
  have hdegF : ∀ n, (f.poly n).totalDegree ≤ n ^ a + a := fun n => by
    rw [hfg n]
    refine totalDegree_finsetSum_le fun e _ =>
      (NS1.totalDegree_aeval_le _ _ fun i => ?_).trans (ha n).2.1
    rcases i with x | i
    · simp
    · simp only [Sum.elim_inr]
      split_ifs <;> simp
  refine ⟨⟨polyBounded_of_le a fun n => (Nat.le_add_right _ _).trans (hcard n),
      polyBounded_of_le a fun n => (totalDegree_toIndep_le f n).trans (hdegF n)⟩,
    G, ⟨⟨polyBounded_of_le a hcard,
      polyBounded_of_le a fun n => (totalDegree_rename_le _ _).trans (ha n).2.1⟩,
      fun n => n ^ a + a, polyBounded_of_le a fun _ => le_rfl, fun n => ?_⟩,
    fun n => ⟨Nat.le_add_right _ _, ?_⟩⟩
  · obtain ⟨Γ, hΓ⟩ := circuit_of_computes (computes_rename (eG n) (ha n).2.2)
    exact ⟨_, le_rfl, Γ, hΓ⟩
  · exact (congrArg _ (hfg n)).trans (booleanSum_eq _ (r n) (g n))

/-! ## The five claims -/

theorem bridge_main : Independent.MainLowerBound.{u} := by
  obtain ⟨c, hc, h⟩ := Solution.mainTheorem.{u}
  refine ⟨c, hc, fun p => ?_⟩
  obtain ⟨m₀, hm₀⟩ := h p
  refine ⟨max m₀ 2, fun F _ _ m hm => ⟨fun k Γ hΓ => ?_, fun hp k Γ hΓ => ?_⟩⟩
  · have := computes_of_circuit Γ hΓ
    rw [hamCycle_eq F (le_of_max_le_right hm)] at this
    exact (hm₀ F m (le_of_max_le_left hm) k).1 this
  · have := computes_of_circuit Γ hΓ
    rw [permanent_eq] at this
    exact (hm₀ F m (le_of_max_le_left hm) k).2 hp this

theorem bridge_border : Independent.MainLowerBoundBorder.{u} := by
  obtain ⟨c, hc, h⟩ := Solution.mainTheoremApprox.{u}
  refine ⟨c, hc, fun p => ?_⟩
  obtain ⟨m₀, hm₀⟩ := h p
  refine ⟨max m₀ 2, fun F _ _ m hm => ⟨fun k Γ hΓ => ?_, fun hp k Γ hΓ => ?_⟩⟩
  · have := approximates_of_circuit (Equiv.refl _) Γ hΓ
    rw [Equiv.coe_refl, rename_id_apply, hamCycle_eq F (le_of_max_le_right hm)] at this
    exact (hm₀ F m (le_of_max_le_left hm) k).1 this
  · have := approximates_of_circuit (Equiv.refl _) Γ hΓ
    rw [Equiv.coe_refl, rename_id_apply, permanent_eq] at this
    exact (hm₀ F m (le_of_max_le_left hm) k).2 hp this

theorem bridge_sep : Independent.VP_ssubset_VNP.{u} := fun F _ => by
  obtain ⟨f, hf, hnf⟩ := Set.exists_of_ssubset (Solution.separation.{u} F)
  exact ⟨Independent.VP_subset_VNP, fun h => hnf (mem_VP_of_toIndep (h (toIndep_mem_VNP hf)))⟩

theorem bridge_closure : Independent.VNP_not_subset_VPbar.{u} := fun F _ h => by
  obtain ⟨f, hf, hnf⟩ := Set.not_subset.1 (Solution.separationClosure.{u} F)
  exact hnf (mem_VPBar_of_toIndep (h (toIndep_mem_VNP hf)))

theorem bridge_real : Independent.PermanentRealLowerBound := by
  obtain ⟨c, hc, m₀, h⟩ := Solution.permanent_over_real
  exact ⟨c, hc, m₀, fun m hm k Γ hΓ =>
    h m hm k (by rw [← permanent_eq]; exact computes_of_circuit Γ hΓ)⟩

end Bridge

end

#print axioms Bridge.bridge_main
#print axioms Bridge.bridge_border
#print axioms Bridge.bridge_sep
#print axioms Bridge.bridge_closure
#print axioms Bridge.bridge_real
