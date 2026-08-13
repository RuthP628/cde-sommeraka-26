import Mathlib

open Function

/-! ## Mit Mengen arbeiten ## -/

/- # Mengenlehre

Die meisten Objekte, die in der Mathematik normalerweise als Mengen konstruiert
werden, sind in Lean Typen. (z.B. ℕ).
Möchten wir explizit über Mengen reden, so müssen alle Elemente in einer Menge
in Lean zum selben Typen gehören.

Dazu gibt es in Lean das Keyword `Set`. Wenn `α` ein Typ ist,
ist `Set α` der Typ der Mengen mit Elementen in `α`.
Wir können uns `Set α` als "Potenzmenge von `α`" vorstellen,
auch wenn das mathematisch nicht ganz korrekt ist.

Lokale Annahmen der Form `s : Set α` kann man also verstehen als
"`s` ist eine Menge, deren Elemente in `α` liegen"
-/

#check Set
#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

#check x ∈ s       -- \in oder \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub


#check s ∩ t       -- \inter oder \cap
#check s ∪ t       -- \union oder \cup
#check s \ t       -- \\ oder \setminus
#check sᶜ          -- \compl oder \^c
#check (∅ : Set α) -- \empty

#check (Set.univ : Set α)
-- konzeptionell dasselbe wie `α`, aber als Menge und nicht als Typ

open Set

#check (univ : Set α)

/- Um zu zeigen, dass `x` ein Element von `s ∩ t`, `s ∪ t` oder `sᶜ` ist,
kann man die folgenden Lemmata verwenden, die den Definitionen der entsprechenden
Konstruktion entsprechen. -/

#check mem_inter_iff x s t
#check mem_union x s t
#check mem_compl_iff s x

#check mem_univ x


/- Die Symbole `∩` und `∪` entsprechen den logischen Symbolen `∧` und `∨`.
Dementsprechend kann man die Taktiken für Konjunktionen und Disjunktionen von Aussagen
direkt auf Schnitte und Vereinigungen von Mengen übertragen:-/

example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  constructor
  · assumption
  · assumption

example (hxs : x ∈ s) : x ∈ s ∪ t := by
  left
  assumption

/- `s ⊆ t` bedeutet, dass für alle `x ∈ s` auch `x ∈ t`gilt: -/

#check subset_def

example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  intro x hx
  obtain ⟨hxs, hxt⟩ := hx
  constructor
  · assumption
  · left
    assumption

/- ## Gleichheit von Mengen

Um zu zeigen, dass zwei Mengen gleich sind, kann man `subset_antisymm`
oder die Taktik `ext` verwenden.

`ext x` ersetzt `s = t` durch die Aussage `x ∈ s ↔ x ∈ t`
für eine neue Variable `x` des richtigen Typs.
-/

#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by
  ext x
  constructor
  all_goals
  intro hx
  exact ⟨ hx.2, hx.1 ⟩

-- Die Taktik `ext` kann man auch für Funktionen verwenden:
-- `(f = g) ↔ ∀ x, f x = g x`


/- Durch Library Search kann man existierende Lemmata über Mengen finden: -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by
  have h₁ : (s ∪ tᶜ) ∩ t = (s ∩ t) ∪ (tᶜ ∩ t) := by rw [@union_inter_distrib_right]
  have h₂ : (s ∩ t) ∪ (tᶜ ∩ t) = s ∩ t ∪ ∅ := by rw [@compl_inter_self]
  have h₃ : s ∩ t ∪ ∅ = s ∩ t := by rw [@union_empty]
  rw [h₁, h₂, h₃]


/- Achtung: Zwei Objekte in Lean sind nur dann gleich, wenn sie auch denselben Typen haben.
So ist `1 : ℕ` nicht dasselbe wie `1 : ℝ`.

Für zwei Objekte von unterschiedlichen Typen kann man Gleichheit nicht einmal staten,
Lean wirft sofort einen Fehler.

Insbesondere ergibt die `≠`- Relation in Lean nur für zwei Objekte vom selben Typ Sinn. -/

-- example (α β : Type*) (x : α) (y : β) : x ≠ y := by sorry

/-
# Set-builder notation
-/

def Evens := {n : ℕ | Even n}
def Odds : Set ℕ := {n | Odd n}

example : Evensᶜ = Odds := by {
  unfold Evens Odds
  ext n
  simp only [mem_compl_iff, mem_ofPred_eq, Nat.not_even_iff_odd]
}


example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x : α | x ∉ s} := by rfl

set_option linter.unusedVariables false in
example : (∅ : Set α) = {x | False} := by rfl

set_option linter.unusedVariables false in
example : (univ : Set α) = {x | True} := by rfl

/- Wir können Bilder und Urbilder von Mengen unter Funktionen betrachten:

`f ⁻¹' s` ist das Urbild von `s` unter `f`.
`f '' s` ist das Bild von `s` unter `f`.

Auf Papier würdet ihr vielleicht `f(A)` oder `f[A]` für das Bild
und `f⁻¹(B)` oder `f⁻¹[B]` für das Urbild schreiben.

Diese Notation ist allerdings uneindeutig,
da wir nicht zwischen Funktionswerten und Bildern unterscheiden,
was der Grund ist, dass wir in Lean eine andere Notation verwenden:
-/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    have hx' : f x ∈ f '' s := by exact mem_image_of_mem f hx
    apply h at hx'
    exact hx'
  · intro h x hx
    have hx' : ∃ y ∈ s, f y = x := by exact hx
    obtain ⟨ y, hy₁, hy₂ ⟩ := hx'
    rw [← hy₂]
    apply h at hy₁
    exact hy₁

/- **Aufgaben** -/

/- Zeige die folgenden Aussagen über Mengen: -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
   unfold image
   unfold preimage

   sorry
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
   sorry
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
    intro x hx
    obtain ⟨ hx₁, hx₂ ⟩ := hx
    obtain ⟨ y₁, hy₁, hy₁' ⟩ := hx₁
    obtain ⟨ y₂, hy₂, hy₂' ⟩ := hx₂
    rw [← hy₂'] at hy₁'
    unfold Injective at h
    apply h at hy₁'
    use y₁
    constructor
    · constructor
      · exact hy₁
      · rw [hy₁']
        exact hy₂
    · rw [hy₁']
      exact hy₂'
  }

/- Wir wollen nun den Satz von Cantor beweisen:

Es gibt keine surjektive Funktion von einer Menge in ihre Potenzmenge.
Tipp: Nutze `let R := {x | x ∉ f x}`, um die Menge `R` zu betrachten,
die alle `x` enthält, die nicht in ihrem Bild unter `f` liegen.
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  sorry
  }
