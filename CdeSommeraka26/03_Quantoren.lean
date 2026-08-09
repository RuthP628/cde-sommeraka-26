import Mathlib

set_option linter.style.header false

/- **Quantoren** -/

/- ## Existenzquantoren -/

/-
Um eine Aussage der Form `∃ x, P x` zu beweisen,
geben wir ein `x₀` vom richtigen Typ an und verwenden die Taktik `use x₀`.
Anschließend zeigen wir `P x₀`.

Um eine lokale Annahme der Form `h : ∃ x, P x` zu verwenden,
nutzen wir `obtain ⟨x₀, hx₀⟩ := h`, um ein `x₀` zu erhalten, das `P` erfüllt.
-/

example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
    sorry

lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
    sorry
  }

/- ## Allquantoren
Die Taktiken für Allquantorn entsprechen denen für Implikationen:
* Wenn unser Ziel von der Form `∀ x, P x` ist, können wir `intro x` benutzen,
  um ein `x` vom richtigen Typ einzuführen, von dem wir nun zeigen müssen, dass `P x` gilt.
* Um lokale Annahmen auf Objekte vom richtigen Typ anzuwenden,
  können wir `apply` und `specialize` benutzen.
-/


def Injective (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f x = f y → x = y


example (f g : ℝ → ℝ) (hg : Injective g)
    (hf : Injective f) :
    Injective (g ∘ f) := by {
    unfold Injective
    unfold Injective at hg
    unfold Injective at hf
    intro x y
    specialize hf x
    specialize hf y
    specialize hg (f x) (f y)
    simp only [Function.comp_apply]
    intro h
    apply hg at h
    apply hf at h
    assumption
  }

/- ## Verhältnis von Negationen und Quantoren -/

/-
Im Fall, dass sowohl Negationen als auch Quantoren in unserer Aussage vorkommen,
können wir mithilfe der folgenden Taktiken das Gesetz vom ausgeschlossenen Dritten verwenden:

* `by_contra h` beginnt einen Widerspruchsbeweis.
* `by_cases h : p` beginnt eine Fallunterscheidung, ob die Aussage `p` gilt oder nicht gilt.
* `push Not` kann verwendet werden, um Negationen "in den Scope von Quantoren hineinzuziehen"
-/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  -- intro hp
  -- by_contra hq
  -- exact h hq hp
  sorry

example (p q r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by
  -- by_cases hp : p
  -- · exact h1 hp
  -- · exact h2 hp
  sorry

example {α : Type*} {p : α → α → Prop} :
    ¬ (∃ x y, p x y) ↔ ∀ x y, ¬ p x y := by
  -- push Not
  -- rfl
  sorry

/-  **Aufgaben**-/

example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
    sorry
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
    sorry
  }

example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
    sorry
  }

example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
    sorry
  }

/- Zeige die folgende Aussage, ohne `push_neg` zu verwenden.
Du wirst im Beweis `by_contra` verwenden müssen. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
    sorry
  }
