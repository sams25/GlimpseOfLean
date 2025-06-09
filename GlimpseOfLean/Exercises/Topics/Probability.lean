import Mathlib.Probability.Notation
import GlimpseOfLean.Library.Probability
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
noncomputable section
open scoped ENNReal
/-

# Probability measures, independent sets

We introduce a probability space and events (measurable sets) on that space. We then define
independence of events and conditional probability, and prove results relating those two notions.

Mathlib has a (different) definition for independence of sets and also has a conditional measure
given a set. Here we practice instead on simple new definitions to apply the tactics introduced in
the previous files.
-/

/- We open namespaces. The effect is that after that command, we can call lemmas in those namespaces
without their namespace prefix: for example, we can write `inter_comm` instead of `Set.inter_comm`.
Hover over `open` if you want to learn more. -/
open MeasureTheory ProbabilityTheory Set

/-
# [sigma algebra, measurable space]
If E is a set, a *sigma algebra* E' on E is a collection of subsets of E such that
- ∅ ∈ E'
- A ∈ E' => Aᶜ ∈ E'
- a countable union of things in E' is in E'.
Then, (E', E) is a *measurable space*.

# [measure, measure space]
A *measure* on a measurable space (E', E) is a function μ: E -> [0, ∞] such that
- μ(∅) = 0,
- countable additivity: μ (countable union of A_i) = countable sum (μ (A_i)).
A *measure space* is a measurable space along with a measure on it, so written as a triple (E', E, μ).

# [probability measure]
A *probability measure* is a measure space (Ω, F, P) where the probability measure P satisfies P(F) = 1.

-/
/- We define a measure space `Ω`: the `MeasureSpace Ω` variable states that `Ω` is a measurable
space on which there is a canonical measure `volume`, with notation `ℙ`.
We then state that `ℙ` is a probability measure. That is, `ℙ univ = 1`, where `univ : Set Ω` is the
universal set in `Ω` (the set that contains all `x : Ω`). -/
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- `A, B` will denote sets in `Ω`.
variable {A B : Set Ω}

/- One can take the measure of a set `A`: `ℙ A : ℝ≥0∞`.
`ℝ≥0∞`, or `ENNReal`, is the type of extended non-negative real numbers, which contain `∞`.
Measures can in general take infinite values, but since our `ℙ` is a probability measure,
it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top`
or `measure_lt_top` to prove that `ℙ A ≠ ∞` or `ℙ A < ∞`.

Hint: use `#check measure_ne_top` to see what that lemma does.

The operations on `ENNReal` are not as nicely behaved as on `ℝ`: `ENNReal` is not a ring and
subtraction truncates to zero for example. If you find that lemma `lemma_name` used to transform
an equation does not apply to `ENNReal`, try to find a lemma named something like
`ENNReal.lemma_name_of_something` and use that instead. -/

#check measure_ne_top
#check measure_lt_top

/-- Two sets `A, B` are independent for the ambient probability measure `ℙ` if
`ℙ (A ∩ B) = ℙ A * ℙ B`. -/
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

/-- If `A` is independent of `B`, then `B` is independent of `A`. -/
lemma IndepSet.symm : IndepSet A B → IndepSet B A := by
  intro h
  rw[IndepSet] at *
  calc
    ℙ (B ∩ A) = ℙ (A ∩ B) := by rw[inter_comm]
    _ = ℙ A * ℙ B := by exact h
    _ = ℙ B * ℙ A := by exact CommMonoid.mul_comm (ℙ A) (ℙ B)

/- Many lemmas in measure theory require sets to be measurable (`MeasurableSet A`).
If you are presented with a goal like `⊢ MeasurableSet (A ∩ B)`, try the `measurability` tactic.
That tactic produces measurability proofs. -/

#check compl_eq_univ_diff
#check measure_diff

-- Hints: `compl_eq_univ_diff`, `measure_diff`, `inter_univ`, `measure_compl`, `ENNReal.mul_sub`
lemma IndepSet.compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by
      intro h
      rw[IndepSet] at *
      rw[measure_compl]
      rw[measure_univ]
      rw[ENNReal.mul_sub]
      rw[mul_one]
      rw[compl_eq_univ_diff]
      rw[inter_diff_distrib_left]
      rw[inter_univ]
      rw[measure_diff]
      rw[h]
      simp
      measurability
      measurability
      measurability
      measurability
      measurability


/- Apply `IndepSet.compl_right` to prove this generalization. It is good practice to add the iff
version of some frequently used lemmas, this allows us to use them inside `rw` tactics. -/
lemma IndepSet.compl_right_iff (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A Bᶜ ↔ IndepSet A B := by
      have hB' : MeasurableSet Bᶜ := by measurability
      constructor
      · intro hab'
        apply IndepSet.compl_right hA hB' at hab'
        rw[← compl_compl B]
        exact hab'
      · intro hab
        exact compl_right hA hB hab

-- Use what you have proved so far
lemma IndepSet.compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B) :
    IndepSet Aᶜ B := by
      apply symm at h
      refine symm ?_
      exact compl_right hB hA h

/- Can you write and prove a lemma `IndepSet.compl_left_iff`, following the examples above?-/

lemma IndepSet.compl_left_iff (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet Aᶜ B <-> IndepSet A B := by
      have hA' : MeasurableSet Aᶜ := by measurability
      constructor
      · intro hab'
        apply IndepSet.compl_left hA' hB at hab'
        rw[← compl_compl A]
        exact hab'
      · intro hab
        exact compl_left hA hB hab

-- Hint: `ENNReal.mul_self_eq_self_iff`
lemma indep_self (h : IndepSet A A) : ℙ A = 0 ∨ ℙ A = 1 := by
  unfold IndepSet at h
  rw[inter_self] at h
  symm at h
  apply (ENNReal.mul_self_eq_self_iff (ℙ A)).mp at h
  simp at h
  exact h

/-

### Conditional probability

-/

/-- The probability of set `A` conditioned on `B`. -/
def condProb (A B : Set Ω) : ENNReal := ℙ (A ∩ B) / ℙ B

/- We define a notation for `condProb A B` that makes it look more like paper math. -/
notation3 "ℙ("A"|"B")" => condProb A B

/- Now that we have defined `condProb`, we want to use it, but Lean knows nothing about it.
We could start every proof with `rw [condProb]`, but it is more convenient to write lemmas about the
properties of `condProb` first and then use those. -/

-- Hint : `measure_inter_null_of_null_left`
@[simp] -- this makes the lemma usable by `simp`
lemma condProb_zero_left (A B : Set Ω) (hA : ℙ A = 0) : ℙ(A|B) = 0 := by
  rw[condProb]
  rw[measure_inter_null_of_null_left]
  simp
  exact hA

/- Why does this not complain for division by 0? Look at the comments after Bayes' Theorem --/
@[simp]
lemma condProb_zero_right (A B : Set Ω) (hB : ℙ B = 0) : ℙ(A|B) = 0 := by
  rw[condProb]
  rw[measure_inter_null_of_null_right]
  simp
  exact hB

/- What other basic lemmas could be useful? Are there other "special" sets for which `condProb`
takes known values? -/

-- Your lemma(s) here

@[simp]
lemma condProb_univ_left (B : Set Ω) (hB: ¬ ℙ B = 0) : ℙ(univ|B) = 1 := by
  rw[condProb]
  rw[univ_inter]
  rw[ENNReal.div_self]
  simp
  exact hB
  simp

@[simp]
lemma condProb_univ_right (A : Set Ω) : ℙ(A|univ) = ℙ A := by
  rw[condProb]
  rw[inter_univ]
  rw[measure_univ]
  simp

/- The next statement is a `theorem` and not a `lemma`, because we think it is important.
There is no functional difference between those two keywords. -/

/-- **Bayes Theorem** -/
theorem bayesTheorem (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  by_cases h : ℙ A = 0 -- this tactic perfoms a case disjunction.
  -- Observe the goals that are created, and specifically the `h` assumption in both goals
  · rw[condProb_zero_left]
    rw[h]
    simp
    exact h
  repeat rw[condProb]
  push_neg at h
  rw[inter_comm]
  congr
  rw[ENNReal.mul_div_cancel]
  exact h
  measurability

/- Did you really need all those hypotheses?
In Lean, division by zero follows the convention that `a/0 = 0` for all a. This means we can prove
Bayes' Theorem without requiring `ℙ A ≠ 0` and `ℙ B ≠ 0`. However, this is a quirk of the
formalization rather than the standard mathematical statement.
If you want to know more about how division works in Lean, try to hover over `/` with your mouse. -/

theorem bayesTheorem' (A B : Set Ω) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  by_cases h : ℙ A = 0 -- this tactic perfoms a case disjunction.
  · rw[condProb_zero_left]
    rw[h]
    simp
    exact h
  · unfold condProb
    push_neg at h
    rw[inter_comm]
    congr
    refine Eq.symm (ENNReal.mul_div_cancel ?_ ?_)
    exact h
    measurability

lemma condProb_of_indepSet (h : IndepSet B A) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A := by
  unfold condProb
  unfold IndepSet at h
  rw[inter_comm] at h
  rw[mul_comm] at h
  calc
    ℙ (A ∩ B) / ℙ B = (ℙ A * ℙ B) / ℙ B := by congr
    _ = ℙ A * (ℙ B / ℙ B) := by exact mul_div_assoc (ℙ A) (ℙ B) (ℙ B)
    _ = ℙ A * 1 := by congr; refine (ENNReal.div_eq_one_iff hB ?_).mpr rfl; measurability
    _ = ℙ A := by simp

