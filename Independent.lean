import Mathlib

/-!
# Superpolynomial lower bounds for HC and the permanent, and VP ≠ VNP (statements only)

An independent formalization of the *statements* of a claimed theorem in algebraic
complexity. Nothing here proves the claim; the five claims are `def … : Prop`.

Sources followed:
* [V79] L. G. Valiant, "Completeness classes in algebra", STOC 1979.
* [B00] P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*,
  Springer 2000, Chapter 2 (straight-line programs, p-families, VP, VNP).
* [BCS] Bürgisser, Clausen, Shokrollahi, *Algebraic Complexity Theory*, Ch. 4
  (straight-line programs) and Ch. 15 (border rank, degenerations).
* [B04] P. Bürgisser, "The complexity of factors of multivariate polynomials",
  FoCM 2004 (approximative complexity and the closure of VP).
* [M13] M. Mahajan, "Algebraic Complexity Classes", arXiv:1307.3863.

Conventions:
* `log` is `Real.logb 2` (base 2).
* Circuit size counts *every* gate: input gates, constant gates, `+` gates and `×` gates.
* Constants: any element of the base ring may label a constant gate (no restriction).
-/

noncomputable section

namespace Independent

open MvPolynomial

universe u v

/-! ## Arithmetic circuits (straight-line programs) -/

/-- A gate of a straight-line program whose `k` earlier gates are indexed by `Fin k`
([B00, Ch. 2], [BCS, Ch. 4], [M13]). A gate is an input variable, a constant
from the coefficient ring `R` (arbitrary constants allowed), or a binary `+` / `×` of two
earlier gates. Fan-out is unbounded since earlier gates can be reused. Subtraction is not
a separate operation: it is expressible with the constant `-1`, as in [B00]. -/
inductive Gate (R : Type u) (σ : Type v) (k : ℕ) : Type (max u v) where
  | input (x : σ)
  | const (c : R)
  | add (a b : Fin k)
  | mul (a b : Fin k)

/-- A circuit (straight-line program) with exactly `k` gates over coefficient ring `R` and
variables `σ`, given as a sequence of gates, each referring only to earlier gates
([B00, Ch. 2]). Its *size* is the index `k`, i.e. the total number of gates, counting input
and constant gates as well as arithmetic gates. (Counting only arithmetic gates, as
[B00] does for `L(f)`, changes sizes by at most a constant factor for circuits without
useless gates, which is absorbed in the constant `c` of the lower bounds.) -/
inductive Circuit (R : Type u) (σ : Type v) : ℕ → Type (max u v) where
  | nil : Circuit R σ 0
  | snoc {k : ℕ} (Γ : Circuit R σ k) (g : Gate R σ k) : Circuit R σ (k + 1)

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- The formal polynomial computed by a gate, given the polynomials of the earlier gates. -/
def Gate.eval {k : ℕ} (prev : Fin k → MvPolynomial σ R) : Gate R σ k → MvPolynomial σ R
  | .input x => X x
  | .const c => C c
  | .add a b => prev a + prev b
  | .mul a b => prev a * prev b

/-- The formal polynomials computed at all gates of a circuit (semantics in the polynomial
ring, [B00, Ch. 2]: the "result sequence" of the straight-line program). -/
def Circuit.values : {k : ℕ} → Circuit R σ k → Fin k → MvPolynomial σ R
  | _, .nil => Fin.elim0
  | _, .snoc Γ g => Fin.snoc (α := fun _ => MvPolynomial σ R) Γ.values (g.eval Γ.values)

/-- A circuit computes `f` if some gate computes `f` as a formal polynomial. (Choosing any
gate as output is equivalent to a designated last output gate, since the gates after it
can be dropped, which only lowers the size.) -/
def Circuit.Computes {k : ℕ} (Γ : Circuit R σ k) (f : MvPolynomial σ R) : Prop :=
  ∃ i, Γ.values i = f

/-- `f` requires circuits of size more than `bound`: every circuit computing `f` has more
than `bound` gates. -/
def RequiresMoreThan (bound : ℝ) (f : MvPolynomial σ R) : Prop :=
  ∀ (k : ℕ) (Γ : Circuit R σ k), Γ.Computes f → bound < k

/-! ## Border (approximative) circuits -/

section Border

variable {F : Type u} [Field F]

/-- Approximative computation ([B04], approximative complexity; cf. border rank in [BCS, Ch. 15]): a circuit with
constants in the rational function field `F(ε)` (here `RatFunc F`, with `ε = RatFunc.X`)
approximates `f ∈ F[x]` if it computes `f + ε·g` for some `g` with coefficients in `F[ε]`.
Equivalently the computed polynomial lies in `F[ε][x]` and specializes to `f` at `ε = 0`.
No bound is placed on the degree in `ε` (the standard, unrestricted notion). -/
def Circuit.Approximates {k : ℕ} (Γ : Circuit (RatFunc F) σ k) (f : MvPolynomial σ F) :
    Prop :=
  ∃ g : MvPolynomial σ (Polynomial F),
    Γ.Computes (map (algebraMap F (RatFunc F)) f +
      C RatFunc.X * map (algebraMap (Polynomial F) (RatFunc F)) g)

/-- `f` has border complexity more than `bound`: every circuit over `F(ε)` that
approximates `f` has more than `bound` gates. -/
def BorderRequiresMoreThan (bound : ℝ) (f : MvPolynomial σ F) : Prop :=
  ∀ (k : ℕ) (Γ : Circuit (RatFunc F) σ k), Γ.Approximates f → bound < k

end Border

/-! ## The Hamiltonian cycle polynomial and the permanent -/

/-- The permanent `per_m = ∑_{π ∈ S_m} ∏_i x_{i,π(i)}` in the `m²` variables
`x_{i,j}`, `(i, j) ∈ Fin m × Fin m` ([V79], [B00, Ch. 2], [M13]). -/
def permanent (R : Type u) [CommSemiring R] (m : ℕ) : MvPolynomial (Fin m × Fin m) R :=
  ∑ π : Equiv.Perm (Fin m), ∏ i, X (i, π i)

/-- The Hamiltonian cycle polynomial `HC_m = ∑ ∏_i x_{i,π(i)}`, the sum over the cyclic
permutations `π ∈ S_m` consisting of a single `m`-cycle ([V79], [B00, Ch. 2], [M13]).
Mathlib's `IsCycle` excludes the identity, so `HC_0 = HC_1 = 0`; this is immaterial for the
asymptotic statements below. -/
noncomputable def hamCycle (R : Type u) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) R := by
  classical
  exact ∑ π ∈ Finset.univ.filter
      (fun π : Equiv.Perm (Fin m) => π.IsCycle ∧ π.support = Finset.univ),
    ∏ i, X (i, π i)

/-- The lower-bound function `m ^ (c · (log₂ m)^(1/3))`, as a real number. -/
noncomputable def lowerBoundFn (c : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (c * (Real.logb 2 m) ^ ((1 : ℝ) / 3))

/-! ## p-families, VP, VNP, VP-bar -/

/-- A function `ℕ → ℕ` is polynomially bounded if it is bounded by a polynomial
([B00, Ch. 2]). -/
def PolyBounded (t : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, t n ≤ p.eval n

/-- A family of polynomials `(f_n)`, `f_n ∈ R[x_0, …, x_{v(n)-1}]` ([B00, Ch. 2]). -/
structure PolyFamily (R : Type u) [CommSemiring R] where
  nvars : ℕ → ℕ
  poly : (n : ℕ) → MvPolynomial (Fin (nvars n)) R

/-- A p-family: number of variables and total degree polynomially bounded
([B00, Ch. 2], [V79]). -/
def IsPFamily (f : PolyFamily R) : Prop :=
  PolyBounded f.nvars ∧ PolyBounded (fun n => (f.poly n).totalDegree)

/-- `VP` ([V79], [B00, Ch. 2, "p-computable"]): p-families whose circuit size is
polynomially bounded. -/
def VP (F : Type u) [Field F] : Set (PolyFamily F) :=
  {f | IsPFamily f ∧ ∃ s : ℕ → ℕ, PolyBounded s ∧
    ∀ n, ∃ k ≤ s n, ∃ Γ : Circuit F (Fin (f.nvars n)) k, Γ.Computes (f.poly n)}

/-- Substitution used in the Boolean sum: the first `v` of the `N` variables stay as
`x_0, …, x_{v-1}`, and variable `v + j` is replaced by the bit `e j ∈ {0,1}`. -/
noncomputable def booleanSubst {F : Type u} [Field F] (v N : ℕ) (e : Fin (N - v) → Bool)
    (j : Fin N) : MvPolynomial (Fin v) F :=
  if h : j.val < v then X ⟨j.val, h⟩
  else C (if e ⟨j.val - v, by have := j.isLt; omega⟩ then 1 else 0)

/-- `∑_{e ∈ {0,1}^{N-v}} g(x_0, …, x_{v-1}, e)`. -/
noncomputable def booleanSum {F : Type u} [Field F] (v N : ℕ) (g : MvPolynomial (Fin N) F) :
    MvPolynomial (Fin v) F :=
  ∑ e : Fin (N - v) → Bool, bind₁ (booleanSubst v N e) g

/-- `VNP`: Valiant's p-definable families ([V79]; [B00, Ch. 2, "p-definable"];
[M13]). `f ∈ VNP` iff `f` is a p-family and there is `g ∈ VP` with
`f_n(x) = ∑_{e ∈ {0,1}^{u(n)}} g_n(x, e)`, where `g_n` has `v(n) + u(n)` variables.
The number of summed bits `u(n)` is polynomially bounded because `g` is a p-family.
We use this definition rather than "p-projections of the permanent / HC" because it is the
original definition and is characteristic-free (the permanent characterization needs
`char F ≠ 2`). -/
def VNP (F : Type u) [Field F] : Set (PolyFamily F) :=
  {f | IsPFamily f ∧ ∃ g ∈ VP F, ∀ n, f.nvars n ≤ g.nvars n ∧
    f.poly n = booleanSum (f.nvars n) (g.nvars n) (g.poly n)}

/-- `VP-bar`, the closure of `VP` ([B04]; also Grochow-Mulmuley-Qiao): p-families
with polynomially bounded border (approximative) complexity over `F(ε)`. -/
def VPbar (F : Type u) [Field F] : Set (PolyFamily F) :=
  {f | IsPFamily f ∧ ∃ s : ℕ → ℕ, PolyBounded s ∧
    ∀ n, ∃ k ≤ s n, ∃ Γ : Circuit (RatFunc F) (Fin (f.nvars n)) k, Γ.Approximates (f.poly n)}

/-! ## The five claims (statements only) -/

/-- Main lower bound (exact circuits). There is an absolute `c > 0` such that for every
characteristic `p` (`p = 0` or prime; other values are vacuous) there is a threshold `m₀`
(depending only on `p`) such that for every field `F` of characteristic `p` and every
`m ≥ m₀`, every circuit over `F` computing `HC_m` has more than `m^(c·(log₂ m)^(1/3))`
gates, and if `p ≠ 2` the same holds for `per_m`. -/
def MainLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p] (m : ℕ),
    m₀ ≤ m →
      RequiresMoreThan (lowerBoundFn c m) (hamCycle F m) ∧
      (p ≠ 2 → RequiresMoreThan (lowerBoundFn c m) (permanent F m))

/-- Main lower bound for border (approximative) circuits, same quantifier structure as
`MainLowerBound`, with circuits over `F(ε)` approximating `HC_m` / `per_m`. -/
def MainLowerBoundBorder : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p] (m : ℕ),
    m₀ ≤ m →
      BorderRequiresMoreThan (lowerBoundFn c m) (hamCycle F m) ∧
      (p ≠ 2 → BorderRequiresMoreThan (lowerBoundFn c m) (permanent F m))

/-- Over every field, `VP` is a strict subset of `VNP`. -/
def VP_ssubset_VNP : Prop :=
  ∀ (F : Type u) [Field F], VP F ⊂ VNP F

/-- Over every field, `VNP` is not contained in `VP-bar`. -/
def VNP_not_subset_VPbar : Prop :=
  ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPbar F

/-- Special case over `ℝ`: there is `c > 0` such that for all sufficiently large `m`, every
real circuit computing `per_m` has more than `m^(c·(log₂ m)^(1/3))` gates. -/
def PermanentRealLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    RequiresMoreThan (lowerBoundFn c m) (permanent ℝ m)

/-! ## Sanity checks (non-vacuity of the definitions) -/

section Sanity

variable {F : Type u} [Field F]

/-- `x₀·x₁` has a circuit with 3 gates: two inputs and one product. -/
theorem x0_mul_x1_size_three :
    ∃ Γ : Circuit F (Fin 2) 3, Γ.Computes (X 0 * X 1) :=
  ⟨((Circuit.nil.snoc (.input 0)).snoc (.input 1)).snoc (.mul 0 1), Fin.last 2, by
    simp [Circuit.values, Gate.eval, Fin.snoc]⟩

/-- `per_2 = x₀₀x₁₁ + x₀₁x₁₀`. -/
theorem permanent_two :
    permanent F 2 = X (0, 0) * X (1, 1) + X (0, 1) * X (1, 0) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  rw [permanent, huniv, Finset.sum_pair hne]
  simp [Fin.prod_univ_two]

/-- `HC_2 = x₀₁x₁₀`: the only 2-cycle is the transposition. -/
theorem hamCycle_two : hamCycle F 2 = X (0, 1) * X (1, 0) := by
  classical
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  have hsupp : (Equiv.swap (0 : Fin 2) 1).support = Finset.univ := by decide
  have hcyc : (Equiv.swap (0 : Fin 2) 1).IsCycle := Equiv.Perm.isCycle_swap (by decide)
  rw [hamCycle]
  convert (Finset.sum_singleton (fun π : Equiv.Perm (Fin 2) => ∏ i, (X (i, π i) :
    MvPolynomial (Fin 2 × Fin 2) F)) (Equiv.swap 0 1)) using 2
  · ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      have : π ∈ ({1, Equiv.swap 0 1} : Finset _) := huniv ▸ Finset.mem_univ π
      rcases Finset.mem_insert.1 this with rfl | h'
      · exact absurd h Equiv.Perm.not_isCycle_one
      · exact Finset.mem_singleton.1 h'
    · rintro rfl
      exact ⟨hcyc, hsupp⟩
  · simp [Fin.prod_univ_two]

/-- The circuit `x, 1, x·1, x·(x·1), …` (`n + 2` gates) whose last gate computes `x^n`. -/
def powCircuit : (n : ℕ) → Circuit F (Fin 1) (n + 2)
  | 0 => (Circuit.nil.snoc (.input 0)).snoc (.const 1)
  | n + 1 => (powCircuit n).snoc (.mul 0 (Fin.last (n + 1)))

theorem powCircuit_zero (n : ℕ) : (powCircuit (F := F) n).values 0 = X 0 := by
  induction n with
  | zero => simp [powCircuit, Circuit.values, Gate.eval, Fin.snoc]
  | succ n ih =>
    simp only [powCircuit, Circuit.values, Fin.snoc]
    simpa using ih

theorem powCircuit_last (n : ℕ) :
    (powCircuit (F := F) n).values (Fin.last (n + 1)) = X 0 ^ n := by
  induction n with
  | zero => simp [powCircuit, Circuit.values, Gate.eval, Fin.snoc]
  | succ n ih =>
    rw [powCircuit, Circuit.values, Fin.snoc_last, Gate.eval, ih, powCircuit_zero, pow_succ,
      mul_comm]

/-- The family `x^n` (one variable, degree `n`). -/
noncomputable def powFamily (F : Type u) [Field F] : PolyFamily F :=
  ⟨fun _ => 1, fun n => X 0 ^ n⟩

theorem powFamily_mem_VP : powFamily F ∈ VP F := by
  refine ⟨⟨⟨Polynomial.C 1, fun n => by simp [powFamily]⟩,
    ⟨Polynomial.X, fun n => by simp [powFamily, MvPolynomial.totalDegree_X_pow]⟩⟩,
    fun n => n + 2, ⟨Polynomial.X + Polynomial.C 2, fun n => by simp⟩,
    fun n => ⟨n + 2, le_rfl, powCircuit n, Fin.last (n + 1), powCircuit_last n⟩⟩

/-- `VP ⊆ VNP` (take the same family with zero summed bits). -/
theorem VP_subset_VNP : VP F ⊆ VNP F := by
  intro f hf
  refine ⟨hf.1, f, hf, fun n => ⟨le_rfl, ?_⟩⟩
  have hsubst : ∀ e, booleanSubst (F := F) (f.nvars n) (f.nvars n) e = X := by
    intro e
    funext j
    simp [booleanSubst, j.isLt]
  simp [booleanSum, hsubst]

end Sanity

end Independent

end
