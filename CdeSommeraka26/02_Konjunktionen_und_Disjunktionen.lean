import Mathlib

set_option linter.style.whitespace false
set_option linter.style.header false

/- **Konjunktionen & Iff**-/
/- In Lean wird die Konjunktion von zwei Aussagen `P` und `Q`
als `P ∧ Q` notiert (sprich: "P und Q").
Das Zeichen `∧` kann als \and oder \wedge eingegeben werden.

Konjunktionen können wie folgt verwendet werden:
* Wenn `h : P ∧ Q` eine Voraussetzung ist, dann ist `h.1`
  ein Beweis für `P` und `h.2` ein Beweis für `Q`.
* Um Aussagen der Form `P ∧ Q` zu beweisen, kann die Taktik
  `constructor` verwendet werden.
  Mit derselben Taktik lässt sich auch ein Ziel der Form `P ↔ Q`
  in `P → Q` und `Q → P` zerlegen.

Falls eine der lokalen Annahmen eine Konjunktion oder Äquivalenz ist,
kann man wie folgt vorgehen:
* Wenn `h : P ∧ Q` eine Annahme ist, erhalten wir mit `obtain ⟨hP, hQ⟩ := h`
  zwei neue lokale Annahmen `hP : P` und `hQ : Q`.
* Wenn `h : P ↔ Q` eine Annahme ist, erhalten wir mit der Taktik `obtain ⟨hPQ, hQP⟩ := h`
  zwei neue lokale Annahmen `hPQ : P → Q` und `hQP : Q → P`. -/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
    -- intro hpq
    -- obtain ⟨ hp, hq ⟩ := hpq
    -- specialize h hp
    -- specialize h' hq
    -- constructor
    -- · assumption
    -- · assumption
    sorry


example (p q : Prop) : p ∧ q ↔ q ∧ p := by
    sorry

/- **Disjunktionen**-/

/-
Das logische ODER wird in Lean als `∨` notiert.
`∨` kann mit der Zeichenfolge \or oder \vee eingegeben werden.

Um ein Ziel der Form `P ∨ Q` direkt zu beweisen,
nutzen wir entweder die Taktik `left` und brauchen nur noch `P` zu beweisen,
oder die Taktik `right`, in diesem Fall genügt es dann, die Aussage `Q` zu beweisen..

Um eine Annahme der Form
  `h : P ∨ Q`
zu nutzen, verwenden wir wieder die `obtain`-Taktik:
  `obtain hP|hQ := h`
Dies kreiert zwei Fälle, die nacheinander abgehandelt werden:
einen Fall mit der Annahme `hP : P` und einen Fall mit der Annahme `hQ : Q`.
-/

variable (a b : ℝ)
#check (mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0)

example : a = a * b → a = 0 ∨ b = 1 := by
  --intro h
  --have h2 : a * (b - 1) = 0 := by linarith
  --have h3 : a = 0 ∨ b - 1 = 0 := mul_eq_zero.1 h2
  --obtain ha|hb := h3
  --· left
  --  exact ha
  --· right
    -- exact sub_eq_zero.1 hb
  --  linarith
  sorry
