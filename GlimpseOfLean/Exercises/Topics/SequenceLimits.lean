import GlimpseOfLean.Library.Basic

namespace Topics

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  linarith

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  linarith

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:
-/

/-- Definition of « u tends to l » -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by
  intro ε ε_pos
  use 0
  intro n n_pos
  calc
    |u n - l| = |l - l| := by rw[h n]
    _ = 0 := by simp
    _ ≤ ε := by exact le_of_lt ε_pos

/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
      rcases h (l/2) (by linarith) with ⟨N, hN⟩
      use N
      intro n hn
      specialize hN n hn
      rw [abs_le] at hN
      linarith

/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
      intros ε ε_pos
      rcases hu ε ε_pos with ⟨N₁, hN₁⟩
      rcases hw ε ε_pos with ⟨N₂, hN₂⟩
      use max N₁ N₂
      intro n hn
      specialize hN₁ n (by exact le_of_max_le_left hn)
      specialize hN₂ n (by exact le_of_max_le_right hn)
      apply abs_le.mpr
      apply abs_le.mp at hN₁
      apply abs_le.mp at hN₂
      constructor
      calc
        -ε ≤ u n - l := by linarith
         _ ≤ v n - l := by linarith [h n]
      calc
        v n - l ≤ w n - l := by linarith [h' n]
              _ ≤ ε := by linarith


/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by
  intro hl hl'
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  rw[seq_limit] at hl
  specialize hl (ε/2) (by linarith)
  rcases hl with ⟨N₁, hN₁⟩
  rw[seq_limit] at hl'
  specialize hl' (ε/2) (by linarith)
  rcases hl' with ⟨N₂, hN₂⟩
  have h₁ := hN₁ (max N₁ N₂) (by exact Nat.le_max_left N₁ N₂)
  have h₂ := hN₂ (max N₁ N₂) (by exact Nat.le_max_right N₁ N₂)
  calc
    |l - l'| = |(l - u (max N₁ N₂)) + (u (max N₁ N₂) - l')| := by ring
    _ ≤ |l - u (max N₁ N₂)| + |u (max N₁ N₂) - l'| := by exact abs_add (l - u (max N₁ N₂)) (u (max N₁ N₂) - l')
    _ = |u (max N₁ N₂) - l| + |u (max N₁ N₂) - l'| := by rw[abs_sub_comm]
    _ ≤ ε/2 + ε/2 := by linarith[h₁, h₂]
    _ = ε := by ring

/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  intros ε ε_pos
  rw[is_seq_sup] at h
  rw[non_decreasing] at h'
  have hr := h.right
  specialize hr ε ε_pos
  rcases hr with ⟨N₁, hN₁⟩
  use N₁
  intros n hn
  rw[abs_le]
  have hn' : u N₁ ≤ u n := by
    apply h'
    exact hn
  have hl := h.left
  have hm := hl n
  constructor
  calc
    -ε ≤ u N₁ - M := by linarith[hN₁]
     _ ≤ u n - M := by linarith[hn']
  calc
    u n - M ≤ 0 := by linarith[hm]
    _ ≤ ε := by exact le_of_lt ε_pos

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction n with
  | zero =>  exact Nat.zero_le (φ 0)
  | succ n ih =>
    have hn : n < n + 1 := by simp
    apply hyp at hn
    calc
      φ (n + 1) > φ n := by exact hn
      _ ≥ n := by apply ih

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  intro hyp N N'
  use max N N'
  constructor
  exact Nat.le_max_right N N'
  calc
    φ (max N N') ≥ max N N' := by apply id_le_extraction' hyp
    _ ≥ N := by exact Nat.le_max_left N N'

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.
-/

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
    intro hyp ε ε_pos N
    rw[cluster_point] at hyp
    rcases hyp with ⟨α, ha⟩
    rcases ha.right ε ε_pos with ⟨N₁, hN₁⟩
    use α (max N N₁)
    constructor
    calc
      α (max N N₁) ≥ max N N₁ := by apply id_le_extraction' ha.left
      _ ≥ N := by exact Nat.le_max_left N N₁
    apply hN₁
    exact Nat.le_max_right N N₁


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N₁, hN₁⟩
  use N₁
  intro n hn
  apply hN₁
  calc
    φ n ≥ φ N₁ := by simp; exact (StrictMono.le_iff_le hφ).mpr hn
    _ ≥ N₁ := by apply id_le_extraction' hφ

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  rcases hl (ε/2) (by exact half_pos ε_pos) with ⟨N₁, hN₁⟩
  rcases ha with ⟨β, hb⟩
  rcases hb.right (ε/2) (by exact half_pos ε_pos) with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hbn : β N ≥ N₁ := by calc
    β N ≥ β N₁ := by simp; exact (StrictMono.le_iff_le hb.left).mpr (Nat.le_max_left N₁ N₂)
    _ ≥ N₁ := by simp; apply id_le_extraction' hb.left
  calc
    |a - l| = |(a - u (β N)) + (u (β N) - l)| := by simp
    _ ≤ |a - u (β N)| + |u (β N) - l| := by exact abs_add_le (a - u (β N)) (u (β N) - l)
    _ = |u (β N) - a| + |u (β N) - l| := by congr 1; apply abs_sub_comm a (u (β N))
    _ ≤ (ε/2) + (ε/2) := by gcongr; apply hN₂ N; exact Nat.le_max_right N₁ N₂; apply hN₁ (β N); apply hbn
    _ = ε := by ring

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  intro h ε ε_pos
  rcases h with ⟨l, hl⟩
  rcases hl (ε/2) (by exact half_pos ε_pos) with ⟨N₁, hN₁⟩
  use N₁
  intro p q hp hq
  calc
    |u p - u q| ≤ |(u p - l) + (l - u q)| := by simp
    _ ≤ |u p - l| + |l - u q| := by exact abs_add_le (u p - l) (l - u q)
    _ = |u p - l| + |u q - l| := by congr 1; apply abs_sub_comm l (u q)
    _ ≤ (ε/2) + (ε/2) := by gcongr; apply hN₁ p; exact hp; apply hN₁ q; exact hq
    _ = ε := by ring

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  intros ε ε_pos
  rw[CauchySequence] at hu
  have hu' := hu (ε/2) (by exact half_pos ε_pos)
  rcases hu' with ⟨N₁, hN₁⟩
  apply near_cluster at hl
  have hl' := hl (ε/2) (by exact half_pos ε_pos)
  use N₁
  intros n' hn'
  rcases (hl' n') with ⟨m, hm⟩
  have hmN₁ : m >= N₁ := by linarith
  specialize hN₁ n' m
  have hmn' : |u n' - u m| ≤ ε/2 := by
    exact hN₁ hn' hmN₁
  calc
    |u n' - l| = |(u n' - u m) + (u m - l)| := by ring
    _ ≤ |u n' - u m| + |u m - l| := by exact abs_add_le (u n' - u m) (u m - l)
    _ ≤ ε/2 + |u m - l| := by linarith[hmn']
    _ ≤ ε/2 + ε/2 := by gcongr; exact hm.right
    _ = ε := by ring
