import Mathlib

set_option linter.style.header false

open Real

/-! ## Aussagen in Lean & Rewriting ##-/

/- Dies ist eine Aussage in Lean: -/

def FermatsLastTheorem : Prop :=
  ∀ a b c n : ℕ, n ≥ 3 → a^n + b^n = c^n → (a = 0 ∨ b = 0 ∨ c=0)

/- D.h. `FermatsLastTheorem` ist der Name eines Objektes vom Typ `Prop` (Proposition).
Das Objekt `FermatsLastTheorem` is definiert als `∀ a b c n : ℕ, n ≥ 3 → ¬ a^n + b^n = c^n`.
Dies entspricht der mathematischen Aussage, dass für `a^n + b^n = c^n`
für alle natürlichen Zahlen `n ≥ 3` keine nichttrivialen Lösungen besitzt. -/

/- Wir können die Aussage auch als ein Theorem in Lean schreiben: -/

theorem FermatsLastTheorem2 :
  ∀ a b c n : ℕ, n ≥ 3 → a^n + b^n = c^n → (a = 0 ∨ b = 0 ∨ c = 0) := sorry

/- In diesem Fall ist das Objekt `FermatsLastTheorem2` kein Objekt vom Typ `Prop`,
sondern ein Objekt vom Typ `∀ a b c n : ℕ, n ≥ 3 → a^n + b^n = c^n → (a = 0 ∨ b = 0 ∨ c = 0)`,
d.h. ein Beweisterm.
Ein Term, den Lean an dieser Stelle als Objekt vom richtigen Typ akzeptiert,
würde also einem Beweis von Fermats letztem Satz entsprechen.

Offenbar haben wir hier jedoch nicht Fermats letzten Satz bewiesen, sondern "geschummelt":
Statt ein Objekt vom richtigen Typen explizit zu konstruieren,
kann man in Lean auch den Platzhalter `sorry` verwenden.
Dann gibt Lean eine Warnung aus, aber akzeptiert das Objekt als ein Objekt vom richtigen Typ. -/

/- Wir können die Aussage auch in der folgenden Form angeben: -/

theorem FermatsLastTheorem3 {a b c n : ℕ} (h : n ≥ 3) : ¬ a^n + b^n = c^n := sorry

/- In diesem Fall sind `a`, `b`, `c` und `n` implizite Argumente
und `h` ist ein explizites Argument vom Typ `n ≥ 3`.
Diese sind alle Teil des lokalen Kontextes.

Im Allgemeinen können wir Aussagen durch Taktiken beweisen.
Die drei einfachsten Taktiken sind:
* `rfl` (reflexivity): Beweist Gleichungen vom Typ `a = a`.
  rfl kann einfache Rechnungen durchführen, z.b. kann man `2 + 2 = 4` mit rfl beweisen.
  (Technical note: rfl beweist Gleichungen, bei denen die rechte und die linke Seite
  entsprechend ihrer typentheoretischen Definition gleich sind).
  Achtung: Nicht alle Gleichungen, bei denen LHS und RHS gleich zu seinen scheinen,
  lassen sich mit `rfl` beweisen.
  Bsp.: `a + b = b + a` kann man nicht mit `rfl` beweisen,
  da es nur in kommutativen Strukturen wahr ist.
* `ring`: beweist Aussagen, die in Ringen (d.h. kommutativen Ringen mit 1) wahr sind.
    `ℤ`, `ℚ`, `ℝ` und `ℂ` sind Ringe, `ℕ` nicht.
* `rw` (rewrite): Ersetzt Teile des Beweises durch Annahmen
  und bereits bewiesene Lemmata im lokalen Kontext.
-/

--Beispiele:

example : 2 + 2 = 4 := by rfl
example (n m : ℤ) : n + m = n + m := by rfl

#check 0

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

example (a b : ℚ) :
  (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
    ring

/-
**Die Taktik rw**
-/

/- Betrachte den folgenden Beweis:-/

example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
  }

/-
Beachte: die Taktik `rw` verändert das aktuelle Ziel. Nach der ersten Zeile im Beweis oben
ist das neue Ziel `b + c + e = d + c`. Wir können also den ersten Schritt lesen als:
"Ich möchte `a + e = d + c` beweisen. Aber da wir nach Annahme `h` wissen, dass `a = b + c` gilt,
reicht es zu zeigen, dass `b + c + e = d + c`".

Man kann auch mehrere `rw`-Operationen in einer Zeile durchführen:
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  sorry

/-
Hinweis: Wenn ihr im obigen Beweis euren Curser zwischen `h` und `h'` platziert,
siehst du das Ziel nach dem `rw` von `h`, aber vor dem `rw` von `h'`.

Im Tactic State sieht man außerdem immer in grün, was sich zuletzt geändert hat,
und in rot, an welchen Stellen die nächste Zeile Änderungen vornehmen wird.

Jetzt seid ihr dran! Hinweis: Für einfache Rechnungen könnt ihr `ring` verwenden.
Um die lokalen Hypothesen zu verwenden, braucht ihr `rw`, da `ring` diese nicht kennt.
-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry

/- Beachte: `rw` nimmt immer die linke Seite von Hypothesen und ersetzt sie durch die rechte Seite.
Aber was, wenn in unserem Ziel nur die rechte Seite einer Annahme vorkommt?
In diesem Fall können wir `← ` (Eingabe durch `\<-`) in den eckigen Klammern
vor die verwendete Annahme schreiben.
Beispiel: -/

example (a b c : ℝ) (h : b + c = a) : a + b = 2 * b + c := by
  sorry

/- Beachte, dass `rw` alle _all_ Vorkommen der linken Seite einer gegebenen Annahme
im Ziel durch die rechte Seite der entsprechenden Annahme ersetzt.
Manchmal ist das aber nicht, was wir wollen.
In diesen seltenen Fällen kann man die `nth_rewrite`-Taktik nutzen,
um Lean zu sagen, dass nur das erste, zweite oder dritte Vorkommen ersetzt werden soll: -/

example (a b c : ℝ) (h : b = c) : a + b + c = a + b + b := by
  sorry

/-

**rw mit Lemmata**

Bislang haben wir `rw` immer nur verwendet, um die lokalen Hypothesen zu verwenden,
allerdings kann man `rw` auch verwenden, um Lemmata aus mathlib,
der mathematischen Standardbibliothek von Lean zu verwenden.
Als Beispiel werden wir im Folgenden eine Aussage über die Exponentialfunktion beweisen.
Um die folgende Aussage zu beweisen, werden wir zweimal das Lemma `exp_add x y` verwenden.
Dies ist ein Beweis, dass `exp(x+y) = exp(x) * exp(y)` gilt.
Hierbei bezeichnet `exp x` die Exponentialfunktion auf den reellen Zahlen (d.h. `e^x`).
-/

#check exp_add

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  sorry

/-
Beachte: Nach dem zweiten `rw` ist das Ziel
`exp a * exp b * exp c = exp a * exp b * exp c` und Lean akzeptiert den Beweis direkt.
Das liegt daran, dass `rw` auch Aussagen der Form `a = a` beweisen kann.
Dabei hat `rw` allerdings eine strengere Auffassung von "Gleichheit" als `rfl`.
-/

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  sorry

/-
Für die folgende Aufgabe werdet ihr die folgenden Lemmata brauchen:
`exp_sub x y : exp(x - y) = exp(x) / exp(y)` und `exp_zero : exp 0 = 1`.

Erinnerung: `a + b - c` steht für `(a + b) - c`.

Hier könnte es nützlich sein, `rw` mit der rechten Seite eines Lemmas zu verwenden.
-/

#check exp_sub
#check exp_zero

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  sorry


/- Beweise die folgende Gleichung mit `rw`. Benutze nicht `ring`!
Hier könnte die `nth_rewrite`-Taktik nützlich sein.

Die folgenden beiden Lemmata beschreiben die Assoziativität und Kommutativität der Multiplikation
in den reellen Zahlen: -/

#check (mul_assoc : ∀ a b c : ℝ, a * b * c = a * (b * c))
#check (mul_comm : ∀ a b : ℝ, a * b = b * a)

example (a b c : ℝ) : a * b * c = b * (a * c) := by {
  sorry
  }

/-! ## Implications, applying forwards & backwards ## -/

/- Wie wir bereits wissen, werden Implikationen in Lean durch `→` notiert.
(Der Pfeil lässt ich durch \rightarrow im Editor eingeben). -/

/-
**Forwards Reasoning** beschreibt die Beweistechnik,
von den Annahmen auszugehen und aus diesen solange neue Annahmen zu folgern,
bis wir bei der zu beweisenden Aussage ankommen.
In Lean geht das mit der Taktik `have`.

Mit der Taktik `intro` können wir `A` als zusätzliche lokale Annahme einführen,
wenn das Ziel von der Form `A → B` ist.

`exact [insert hypothesis]` und `assumption` können verwendet werden, um einen Beweis zu beenden.
-/

example (p q : Prop) : ((p → q) ∧ p) → q := by
  --intro h
  --have h1 : p → q := h.1
  --have h2 : p := h.2
  --apply h1
  --assumption
  sorry

example (p q r : Prop) (hq : p → q)
    (hr : p → (q → r)) : p → r := by
      sorry

/- `specialize` kann verwendet werden, um eine Annahme
auf eine andere Annahme des lokalen Kontextes anzuwenden. -/
example (p q r : Prop) (hq : p → q) (hr : p → q → r) : p → r := by
  --intro hp
  --specialize hq hp
  --specialize hr hp hq
  --assumption
  sorry

/- Die `apply`-Taktik ist sehr ähnlich zu `specialize`.

Um den Unterschied zwischen den beiden Taktiken zu verstehen, nehmen wir an,
wir haben die beiden Hypothesen `h₁ : p` und `h₂ : p → q` im lokalen Kontext.
Dann lässt `specialize h₂ h₁` die Hypothese `h₁` unverändert und
ändert die Hypothese `h₂` zu `q`.
Währenddessen lässt `apply h₂ at h₁` die Hypothese `h₂` unverändert
und verändert `h₁` zu `q`.
-/

example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by
  --intro hs hp
  --apply hq at hp
  --apply hp at hs
  --apply hr at hs
  --assumption
  sorry

/- Wir können mehrere Schritte in einer Zeile durchführen,
indem wir unsere Kenntnisse zu Lambda Calculus nutzen: -/
example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by
  --intro hs hp
  --exact hr (hq hp hs)
  sorry


/-
**Backwards reasoning** beschreibt die Beweistaktik,
das Ziel solange umzuformen, bis man bei einer der Voraussetzungen ankommt.

Hierfür können wir wieder die `apply`-Taktik nutzen:
Angenommen, unser Ziel ist von der Form `B`
und eine unserer Voraussetzungen ist von der Form `h : A → B`.
Dann können wir `apply h` schreiben, um unser Ziel zu `A` zu ändern.

Achtung: dies garantiert natürlich nicht, dass unser Ziel anschließend immer noch
aus den Voraussetzungen folgt.

Beispielsweise folgt aus der falschen Aussage `False`, jede beliebige Aussage,
aber sofern unsere Voraussetzungen nicht widersprüchlich sind,
werden wir nie `False` beweisen können (dazu später mehr).
-/

example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by
  --intro hs hp
  --apply hr
  --have h : s → q := by apply hq; exact hp
  --apply h
  --assumption
  sorry

#check le_of_lt

example (n : ℕ) (h : n ≤ 5) : n ≤ 5 := by
  -- apply le_of_lt
  -- dead end
  sorry

/-
**Unterschiede zwischen `rw` und `apply`**
- `rw` kann genutzt werden, um die linke Seite einer Hypothese *irgendwo* im Ziel zu ersetzen,
  Währenddessen muss der `apply` das gesamte Ziel verändern, um anwendbar zu sein.
- *Im Allgemeinen* verwendet man `rw` für Gleichungen
  und `apply` für Implikationen und "for all"-statements.
-/

/- **Negation** -/

/- Die Negation `¬ A` steht für `A → False`,
wobei `False` eine Aussage ohne Beweis ist.

Für Negationen können wir dieselben Taktiken benutzen wie für Implikationen:
Um eine Negation zu beweisen, können wir `intro` verwenden,
und um eine Negation zu verwenden, können wir `apply` verwenden. -/

example {p : Prop} (h : p) : ¬ ¬ p := by
  --intro h'
  --apply h'
  --assumption
  sorry

-- *TODO*: Copy the following example to the file about quantifiers
/-
example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  --constructor
  --· intro h x hx
  --  apply h
  --  use x
  --· intro h h2
  --  obtain ⟨x, hx⟩ := h2
  --  exact h x hx
  sorry
  }
-/

/- Die Taktik `exfalso` (steht für "ex falso quod libet", d.h. "aus Falschem folgt beliebiges")
kann verwendet werden, um zu beweisen, aus `False` jede beliebige andere Aussage folgt.

Anwenden der Taktik `exfalso` ersetzt das Ziel durch `False`,
d.h. nun muss gezeigt werden, dass die Annahmen widersprüchlich sind.-/

example {p : Prop} (h : ¬ p) : p → 0 = 1 := by {
  -- intro h2
  -- exfalso
  -- exact h h2
  sorry
  }

/- `contradiction` proves any goal
when two hypotheses are contradictory. -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  --intro hp
  --contradiction
  sorry

/-
**Aufgaben zu rw und Implikationen**
 -/

/- Die folgende Aussage ist überraschend schwierig, überspringt sie gerne, wenn ihr wollt.

Falls ihr sie doch versuchen wollt, könnte das folgende Lemma hilfreich sein.

Allerdings gibt es mehrere Wege, die Aussage zu beweisen,
wundert euch nicht, wenn ihr das Lemma nicht braucht.-/

#check mul_eq_zero.1


example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  have h3 : a - b + 3 * b = 4 := by rw [← h1]; ring
  rw [h2] at h3

  sorry

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
    sorry
  }
