import Lax512892.Locality
import Mathlib.Data.Fintype.Basic

/-!
---
title: Gaifman's normal-form theorem
type: theorem
---
Every first-order formula over a finite relational vocabulary has an effective,
uniform translation into a Boolean combination of formulas local around its
free tuple and basic local sentences. At radius `r`, a basic local sentence
asserts that there are `s` witnesses, pairwise at Gaifman distance greater than
`2r`, all satisfying the same one-variable `r`-local formula.

If the input has quantifier rank `q` and `k` free variables, the radius can be
chosen at most `7^q`, and every basic local sentence needs at most `q + k`
witnesses. When the input is a sentence, every constituent of the normal form
is itself a sentence. This closedness condition is enforced by the index of
`NormalForm`: a value of type `NormalForm σ 0` can contain only zero-anchor
local formulas and basic local sentences. The equivalence is over all finite
structures.

This is the uniform formulation of Gaifman's theorem used in Theorem 4.22 of
Libkin's *Elements of Finite Model Theory*, following Gaifman's original
locality theorem.

# Formalization notes

The output syntax is reified. `NormalForm σ k` is a Boolean combination whose
atoms are either local formulas around the `k` free variables or basic local
sentences; every atom records its own radius. This permits the uniform radius
bound and the witness bound to be stated directly about every atom that occurs,
without incorrectly requiring unrelated constituents to use one common radius.
In the sentence case `k = 0`, closedness follows from the syntax rather than
from excluding zero-anchor local formulas; such closed local formulas are
needed, for example, to express quantifier-free facts about constants or
nullary relations.

The theorem quantifies once over a single translation function, before any
input formula or structure. This records uniformity more faithfully than a
separate existential normal form for each formula. It does not assert a running
time bound for the translation. A constructive proof of the axiom supplies the
effective transformation; code extraction is not part of the concept surface.

The `s = 0` basic sentence is allowed and is vacuously true, exactly as the
displayed first-order sentence with an empty witness tuple. Pairwise separation
is imposed only for distinct witness indices.
-/

namespace Lax512892.GaifmanNormalForm

open Lax512892.RelationalStructures Lax512892.FirstOrder Lax512892.Locality

universe u

/-- Boolean combinations of atoms of type `α`. -/
inductive BooleanCombination (α : Type u) : Type u
  /-- An atomic constituent. -/
  | atom (a : α)
  /-- Truth, serving also as the empty Boolean combination. -/
  | truth
  /-- Negation. -/
  | not (b : BooleanCombination α)
  /-- Conjunction. -/
  | and (b c : BooleanCombination α)

namespace BooleanCombination

/-- Evaluation of a Boolean combination from an interpretation of its atoms. -/
def eval {α : Type u} (value : α → Prop) : BooleanCombination α → Prop
  | .atom a => value a
  | .truth => True
  | .not b => ¬ b.eval value
  | .and b c => b.eval value ∧ c.eval value

/-- The atoms occurring in a Boolean combination, with multiplicity. -/
def atoms {α : Type u} : BooleanCombination α → List α
  | .atom a => [a]
  | .truth => []
  | .not b => b.atoms
  | .and b c => b.atoms ++ c.atoms

end BooleanCombination

/-- A basic local sentence at radius `r`: `witnessCount` pairwise far-apart
witnesses all satisfy the same one-variable local formula `property`. -/
structure BasicLocalSentence (σ : Vocabulary) (r : ℕ) where
  /-- The number of witnesses. -/
  witnessCount : ℕ
  /-- The uniform local property required of every witness. -/
  property : LocalFormula σ 1 r 0

namespace BasicLocalSentence

/-- Semantics of a basic local sentence. -/
def Sat {σ : Vocabulary} {M : Type*} {r : ℕ} (A : Structure σ M)
    (β : BasicLocalSentence σ r) : Prop :=
  ∃ witnesses : Fin β.witnessCount → M,
    (∀ i, β.property.Sat A (fun _ => witnesses i) Fin.elim0) ∧
      ∀ i j, i ≠ j →
        ¬ distanceAtMost A (2 * r) (witnesses i) (witnesses j)

end BasicLocalSentence

/-- An atom of a Gaifman normal form. Each atom carries its own locality
radius. -/
inductive NormalAtom (σ : Vocabulary) (k : ℕ) : Type
  /-- A formula local around the `k` free variables. -/
  | local (r : ℕ) (formula : LocalFormula σ k r 0)
  /-- A basic local sentence. -/
  | basic (r : ℕ) (sentence : BasicLocalSentence σ r)

/-- A Gaifman normal form for a formula with `k` free variables. -/
structure NormalForm (σ : Vocabulary) (k : ℕ) where
  /-- A Boolean combination of local formulas and basic local sentences. -/
  body : BooleanCombination (NormalAtom σ k)

namespace NormalForm

/-- Satisfaction of a normal form under an environment for its free variables. -/
def Sat {σ : Vocabulary} {M : Type*} {k : ℕ} (A : Structure σ M)
    (env : Fin k → M) (nf : NormalForm σ k) : Prop :=
  nf.body.eval fun atom =>
    match atom with
    | .local _ ψ => ψ.Sat A env Fin.elim0
    | .basic _ basic => basic.Sat A

/-- Every constituent occurring in `nf` has radius at most `bound`. -/
def RadiiBounded {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) (bound : ℕ) : Prop :=
  ∀ atom : NormalAtom σ k, atom ∈ nf.body.atoms →
    match atom with
    | .local r _ => r ≤ bound
    | .basic r _ => r ≤ bound

/-- Every basic local sentence occurring in `nf` uses at most `bound`
witnesses. -/
def WitnessesBounded {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) (bound : ℕ) : Prop :=
  ∀ (r : ℕ) (basic : BasicLocalSentence σ r),
    NormalAtom.basic r basic ∈ nf.body.atoms → basic.witnessCount ≤ bound

end NormalForm

/-- **Gaifman's normal-form theorem.** There is a uniform transformation of
every first-order formula over `σ` into an equivalent Gaifman normal form. For
an input of quantifier rank `q` with `k` free variables, every constituent has
radius at most `7 ^ q`, and each basic local sentence has at most `q + k`
witnesses. If the input is a sentence, the result has type `NormalForm σ 0`, so
every constituent is closed. Equivalence holds in every finite `σ`-structure. -/
axiom gaifmanNormalForm (σ : Vocabulary) :
    ∃ translate : (k : ℕ) → Formula σ k → NormalForm σ k,
      ∀ (k : ℕ) (φ : Formula σ k),
        (translate k φ).RadiiBounded (7 ^ φ.quantifierRank) ∧
        (translate k φ).WitnessesBounded (φ.quantifierRank + k) ∧
        ∀ {M : Type} [Fintype M] (A : Structure σ M) (env : Fin k → M),
          φ.Sat A env ↔ (translate k φ).Sat A env

end Lax512892.GaifmanNormalForm
