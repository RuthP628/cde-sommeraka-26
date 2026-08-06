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
