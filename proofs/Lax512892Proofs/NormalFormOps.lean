import Lax512892Proofs.BooleanCombination

/-!
Elementary constructors for Gaifman normal forms.  This module discharges the
atomic and Boolean cases of the main structural induction; only existential
quantification requires the locality argument.
-/

namespace Lax512892Proofs.NormalFormOps

open Lax512892.RelationalStructures Lax512892.FirstOrder
open Lax512892.Locality Lax512892.GaifmanNormalForm
open Lax512892Proofs.BooleanCombination

universe u

namespace LocalTerm

/-- Regard a first-order term as a term of a local formula with no locally
bound variables. -/
def ofTerm {σ : Vocabulary} {k : ℕ} :
    Term σ k → Lax512892.Locality.LocalTerm σ k 0
  | .var i => .anchor i
  | .const c => .const c

@[simp] theorem eval_ofTerm {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (t : Term σ k) :
    (ofTerm t).eval A env Fin.elim0 = t.eval A env := by
  cases t <;> rfl

end LocalTerm

namespace LocalFormula

/-- Truth as a zero-quantifier local formula.  For an empty anchor context and
constant-free vocabulary there is no term from which to form `t = t`; a
nullary relation atom, when present, is already handled directly.  Thus truth
is needed only by the Boolean-combination layer, whose own `truth` constructor
serves this role without a term. -/
def conjunction {σ : Vocabulary} {k r b : ℕ}
    (φ ψ : Lax512892.Locality.LocalFormula σ k r b) :
    Lax512892.Locality.LocalFormula σ k r b :=
  .not (.or (.not φ) (.not ψ))

/-- A contradiction built from any available local term. -/
def falsity {σ : Vocabulary} {k r b : ℕ}
    (t : Lax512892.Locality.LocalTerm σ k b) :
    Lax512892.Locality.LocalFormula σ k r b :=
  .not (.eq t t)

/-- Finite disjunction, with an explicit false formula for the empty list. -/
def disjunctions {σ : Vocabulary} {k r b : ℕ}
    (falseFormula : Lax512892.Locality.LocalFormula σ k r b) :
    List (Lax512892.Locality.LocalFormula σ k r b) →
      Lax512892.Locality.LocalFormula σ k r b
  | [] => falseFormula
  | φ :: φs => .or φ (disjunctions falseFormula φs)

@[simp] theorem sat_conjunction {σ : Vocabulary} {M : Type*} {k r b : ℕ}
    (A : Structure σ M) (env : Fin k → M) (bound : Fin b → M)
    (φ ψ : Lax512892.Locality.LocalFormula σ k r b) :
    (conjunction φ ψ).Sat A env bound ↔
      φ.Sat A env bound ∧ ψ.Sat A env bound := by
  simp only [conjunction, Lax512892.Locality.LocalFormula.Sat]
  tauto

@[simp] theorem not_sat_falsity {σ : Vocabulary} {M : Type*} {k r b : ℕ}
    (A : Structure σ M) (env : Fin k → M) (bound : Fin b → M)
    (t : Lax512892.Locality.LocalTerm σ k b) :
    ¬ (falsity (r := r) t).Sat A env bound := by
  simp [falsity, Lax512892.Locality.LocalFormula.Sat]

theorem sat_disjunctions {σ : Vocabulary} {M : Type*} {k r b : ℕ}
    (A : Structure σ M) (env : Fin k → M) (bound : Fin b → M)
    (falseFormula : Lax512892.Locality.LocalFormula σ k r b)
    (hfalse : ¬ falseFormula.Sat A env bound)
    (formulas : List (Lax512892.Locality.LocalFormula σ k r b)) :
    (disjunctions falseFormula formulas).Sat A env bound ↔
      ∃ φ ∈ formulas, φ.Sat A env bound := by
  induction formulas with
  | nil => simp [disjunctions, hfalse]
  | cons φ formulas ih =>
      simp only [disjunctions, Lax512892.Locality.LocalFormula.Sat, ih]
      aesop

end LocalFormula

namespace NormalForm

/-- The always-true normal form. -/
def truth (σ : Vocabulary) (k : ℕ) : NormalForm σ k :=
  ⟨.truth⟩

/-- Negation of a normal form. -/
def neg {σ : Vocabulary} {k : ℕ} (nf : NormalForm σ k) : NormalForm σ k :=
  ⟨.not nf.body⟩

/-- Conjunction of normal forms. -/
def conj {σ : Vocabulary} {k : ℕ}
    (left right : NormalForm σ k) : NormalForm σ k :=
  ⟨.and left.body right.body⟩

/-- Disjunction of normal forms. -/
def disj {σ : Vocabulary} {k : ℕ}
    (left right : NormalForm σ k) : NormalForm σ k :=
  ⟨BooleanCombination.or left.body right.body⟩

/-- A normal form consisting of one local atom. -/
def ofLocal {σ : Vocabulary} {k r : ℕ}
    (φ : Lax512892.Locality.LocalFormula σ k r 0) : NormalForm σ k :=
  ⟨.atom (.local r φ)⟩

/-- A normal form consisting of one basic local sentence. -/
def ofBasic {σ : Vocabulary} {k r : ℕ}
    (β : BasicLocalSentence σ r) : NormalForm σ k :=
  ⟨.atom (.basic r β)⟩

@[simp] theorem sat_truth {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) :
    (truth σ k).Sat A env :=
  trivial

@[simp] theorem sat_neg {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (nf : NormalForm σ k) :
    (neg nf).Sat A env ↔ ¬ nf.Sat A env :=
  Iff.rfl

@[simp] theorem sat_conj {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (left right : NormalForm σ k) :
    (conj left right).Sat A env ↔ left.Sat A env ∧ right.Sat A env :=
  Iff.rfl

@[simp] theorem sat_disj {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (left right : NormalForm σ k) :
    (disj left right).Sat A env ↔ left.Sat A env ∨ right.Sat A env := by
  exact eval_or _ _ _

@[simp] theorem sat_ofLocal {σ : Vocabulary} {M : Type*} {k r : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (φ : Lax512892.Locality.LocalFormula σ k r 0) :
    (ofLocal φ).Sat A env ↔ φ.Sat A env Fin.elim0 :=
  Iff.rfl

@[simp] theorem sat_ofBasic {σ : Vocabulary} {M : Type*} {k r : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (β : BasicLocalSentence σ r) :
    (ofBasic (k := k) β).Sat A env ↔ β.Sat A :=
  Iff.rfl

theorem radiiBounded_truth {σ : Vocabulary} {k bound : ℕ} :
    (truth σ k).RadiiBounded bound := by
  intro atom h
  simp [truth, Lax512892.GaifmanNormalForm.BooleanCombination.atoms] at h

theorem radiiBounded_neg {σ : Vocabulary} {k bound : ℕ}
    {nf : NormalForm σ k} (h : nf.RadiiBounded bound) :
    (neg nf).RadiiBounded bound := by
  intro atom ha
  exact h atom ha

theorem radiiBounded_conj {σ : Vocabulary} {k bound : ℕ}
    {left right : NormalForm σ k}
    (hl : left.RadiiBounded bound) (hr : right.RadiiBounded bound) :
    (conj left right).RadiiBounded bound := by
  intro atom ha
  simp only [conj, Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl atom) (hr atom)

theorem radiiBounded_disj {σ : Vocabulary} {k bound : ℕ}
    {left right : NormalForm σ k}
    (hl : left.RadiiBounded bound) (hr : right.RadiiBounded bound) :
    (disj left right).RadiiBounded bound := by
  intro atom ha
  simp only [disj, BooleanCombination.or,
    Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl atom) (hr atom)

theorem radiiBounded_ofLocal {σ : Vocabulary} {k r bound : ℕ}
    (φ : Lax512892.Locality.LocalFormula σ k r 0) (hr : r ≤ bound) :
    (ofLocal φ).RadiiBounded bound := by
  intro atom ha
  simp only [ofLocal, Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_singleton] at ha
  subst atom
  exact hr

theorem radiiBounded_ofBasic {σ : Vocabulary} {k r bound : ℕ}
    (β : BasicLocalSentence σ r) (hr : r ≤ bound) :
    (ofBasic (k := k) β).RadiiBounded bound := by
  intro atom ha
  simp only [ofBasic, Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_singleton] at ha
  subst atom
  exact hr

theorem witnessesBounded_truth {σ : Vocabulary} {k bound : ℕ} :
    (truth σ k).WitnessesBounded bound := by
  intro r basic h
  simp [truth, Lax512892.GaifmanNormalForm.BooleanCombination.atoms] at h

theorem witnessesBounded_neg {σ : Vocabulary} {k bound : ℕ}
    {nf : NormalForm σ k} (h : nf.WitnessesBounded bound) :
    (neg nf).WitnessesBounded bound := by
  intro r basic ha
  exact h r basic ha

theorem witnessesBounded_conj {σ : Vocabulary} {k bound : ℕ}
    {left right : NormalForm σ k}
    (hl : left.WitnessesBounded bound) (hr : right.WitnessesBounded bound) :
    (conj left right).WitnessesBounded bound := by
  intro r basic ha
  simp only [conj, Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl r basic) (hr r basic)

theorem witnessesBounded_disj {σ : Vocabulary} {k bound : ℕ}
    {left right : NormalForm σ k}
    (hl : left.WitnessesBounded bound) (hr : right.WitnessesBounded bound) :
    (disj left right).WitnessesBounded bound := by
  intro r basic ha
  simp only [disj, BooleanCombination.or,
    Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl r basic) (hr r basic)

theorem witnessesBounded_ofLocal {σ : Vocabulary} {k r bound : ℕ}
    (φ : Lax512892.Locality.LocalFormula σ k r 0) :
    (ofLocal φ).WitnessesBounded bound := by
  intro radius basic h
  simp [ofLocal, Lax512892.GaifmanNormalForm.BooleanCombination.atoms] at h

theorem witnessesBounded_ofBasic {σ : Vocabulary} {k r bound : ℕ}
    (β : BasicLocalSentence σ r) (hβ : β.witnessCount ≤ bound) :
    (ofBasic (k := k) β).WitnessesBounded bound := by
  intro radius basic h
  simp only [ofBasic, Lax512892.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_singleton, NormalAtom.basic.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact hβ

end NormalForm

/-- A relation atom is already local (with radius zero). -/
def relationAtomNormalForm {σ : Vocabulary} {k : ℕ} (R : σ.Relation)
    (args : Fin (σ.arity R) → Term σ k) : NormalForm σ k :=
  NormalForm.ofLocal (r := 0) (.rel R (fun i => LocalTerm.ofTerm (args i)))

/-- An equality atom is already local (with radius zero). -/
def equalityAtomNormalForm {σ : Vocabulary} {k : ℕ}
    (left right : Term σ k) : NormalForm σ k :=
  NormalForm.ofLocal (r := 0)
    (.eq (LocalTerm.ofTerm left) (LocalTerm.ofTerm right))

@[simp] theorem sat_relationAtomNormalForm {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (R : σ.Relation)
    (args : Fin (σ.arity R) → Term σ k) :
    (relationAtomNormalForm R args).Sat A env ↔ Formula.Sat A (.rel R args) env := by
  simp only [relationAtomNormalForm, NormalForm.sat_ofLocal,
    Lax512892.Locality.LocalFormula.Sat, Formula.Sat, LocalTerm.eval_ofTerm]

@[simp] theorem sat_equalityAtomNormalForm {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (left right : Term σ k) :
    (equalityAtomNormalForm left right).Sat A env ↔
      Formula.Sat A (.eq left right) env := by
  simp only [equalityAtomNormalForm, NormalForm.sat_ofLocal,
    Lax512892.Locality.LocalFormula.Sat, Formula.Sat, LocalTerm.eval_ofTerm]

end Lax512892Proofs.NormalFormOps
