import Mathlib

set_option linter.style.whitespace false

/-
# Induktive Typen

Induktive Typen sind die Lean-Entsprechung des mathematischen Konzepts einer rekursiven Definition.

Die einfachste Form von induktiven Typen sind "Auflistungen von Elementen".

Die folgende Definition des induktiven Typs `Weekday`
entspricht folgender Aussage in natürlicher Sprache:

"Wochentage sind wie folgt definiert:

Montag ist ein Wochentag.
Dienstag ist ein Wochentag.
Mittwoch ist ein Wochentag.
Donnerstag ist ein Wochentag.
Freitag ist ein Wochentag.
Samstag ist ein Wochentag.
Sonntag ist ein Wochentag."
-/

inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  | sunday : Weekday

/- Funktionen von induktiven Typen zu anderen Typen lassen sich mit der `match`-Syntax
definieren:

Für jeden Konstruktor des induktiven Typs geben wir eine an,
wie der entsprechenden Funktionswert konstruiert wird.  -/

def NumberOfWeekday (d : Weekday) : Nat :=
  match d with
  | .monday => 1
  | .tuesday => 2
  | .wednesday => 3
  | .thursday => 4
  | .friday => 5
  | .saturday => 6
  | .sunday => 7

/- Wenn wir Funktionen tatsächlich als Arrow Type definieren, können wir
statt der `match`-Syntax auch die folgende Syntax verwenden (Beachte das Fehlen von `:=`): -/

def NumberOfWeekday2 : Weekday → Nat
  | .monday => 1
  | .tuesday => 2
  | .wednesday => 3
  | .thursday => 4
  | .friday => 5
  | .saturday => 6
  | .sunday => 7

def NextWeekday (d : Weekday) : Weekday :=
  match d with
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday

def PrevWeekday (d : Weekday) : Weekday :=
  match d with
  | .monday => .sunday
  | .tuesday => .monday
  | .wednesday => .tuesday
  | .thursday => .wednesday
  | .friday => .thursday
  | .saturday => .friday
  | .sunday => .saturday

/- Aussagen über induktive Typen lassen sich ebenfalls mit der Match-Syntax beweisen: -/

lemma NextPrevWeekday (d : Weekday) : NextWeekday (PrevWeekday d) = d := by
  match d with
  | .monday => rfl
  | .tuesday => rfl
  | .wednesday => rfl
  | .thursday => rfl
  | .friday => rfl
  | .saturday => rfl
  | .sunday => rfl

/- Die Taktik `cases` erstellt automatisch ein Subgoal
für jeden Konstruktor eines induktiven Typs. -/

lemma PrevNextWeekday (d : Weekday) : PrevWeekday (NextWeekday d) = d := by
  cases d
  all_goals
  rfl

/- Der tatsächliche Nutzen von induktiven Typen (im Gegensatz zu anderen Typen)
ist allerdings der folgende:

Konstruktoren eines induktiven Typs können von anderen Typen abhängen.
Insbesondere können Konstruktoren eines induktiven Typs Elemente des Typs,
der gerade konstruiert wird, als Inputs nehmen.
Mathematisch entspricht dies einer rekursiven Definition.

Beispielsweise lautet die folgende Definition in natürlicher Sprache:

"Eine Liste mit Elementen aus `α` ist wie folgt definiert:
1.) Die leere Liste ist eine Liste mit Elementen aus `α`
2.) Wenn `list` eine Liste mit Elementen aus `α` und `a` ein Element von `α` ist,
dann können wir `a` links an die Liste `list` anhängen und erhalten eine neue Liste mit Elementen
in `α`." -/

inductive MyList (α : Type*) where
  | empty : MyList α
  | AppendLeft (a : α) (list : MyList α) : MyList α

/- Dies ist tatsächlich auch, wie Listen in Lean normalerweise definiert sind: -/

#check List

/- Induktive Typen können sehr viele verschiedene mathematische Konzepte beschreiben.

Beispielsweise beschreibt der folgende Typ die disjunkte Vereinigung von zwei Typen:
-/

inductive DisjointUnion (α β : Type*) where
  /- Die linke Inklusion bettet `α` in der disjunkten Vereinigung von `α` und `β` ein. -/
  | LeftInclusion : α →  DisjointUnion α β
  /- Die rechte Inklusion bettet `β` in der disjunkten Vereinigung von `α` und `β` ein. -/
  | RightInclusion : β → DisjointUnion α β

/- Die Konstruktion `Sum` in mathlib entspricht der oben definierten disjunkten Vereinigung. -/
#check Sum

/- # Definition der natürlichen Zahlen:

Der wichtigste induktive Typ in Lean sind die natürlichen Zahlen.

In Lean sind diese wie folgt definiert:
1.) `0` ist eine natürliche Zahl.
2.) Für jede natürliche Zahl `n` gibt es einen Nachfolger `n+1`.
 -/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

/- Dies entspricht auch der Definition in Mathlib. -/
#check Nat

/- Die ganzen Zahlen sind wie folgt induktiv definiert:

1.) Jede natürliche Zahl kann als ganze Zahl aufgefasst werden.
2.) Wenn `n` eine natürliche Zahl ist, ist `-(n+1)` eine ganze Zahl. -/
#check Int

/- # Rekursion und Induktion

Das folgende ist eine rekursive Definition der Fakultät.
Die Syntax für solche rekursive Definitionen haben wir bereits bei `NumberOfWeekday2` definiert. -/

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

-- Beachte: Lean überprüft bei rekursiven Definitionen nicht direkt, dass diese wohldefiniert sind.
-- Betrachte dazu folgende (illegale) Definition:
-- def wrong : ℕ → ℕ
--   | 0 => 1
--   | (n + 1) =>
--     -- have : n + 2 < n + 1 := by sorry
--     wrong (n + 2)

-- #eval! wrong 2

lemma fac_zero : fac 0 = 1 := rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl

example : fac 4 = 24 := rfl

#eval fac 100

/- Aussagen über induktive Typen (d.h. meistens natürliche Zahlen)
lassen sich auch mit der Induction Tactic zeigen: -/
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    unfold fac
    norm_num
  | succ n ih =>
    rw [fac]
    positivity

open BigOperators Finset

/- Wir können `∑ i ∈ range (n + 1), f i` schreiben,
um die Summe `f 0 + f 1 + ⋯ + f n` zu beschreiben: -/

example (f : ℕ → ℝ) : ∑ i ∈ range 0, f i = 0 :=
  sum_range_zero f

example (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n :=
  sum_range_succ f n

/- Hier beschreibt `range n` bzw. `Finset.range n` die Menge `{0, ..., n - 1}`.
Es hat den Typ `Finset ℕ`, d.h. eine Menge natürlicher Zahlen zusammen mit der Eigenschaft,
endlich zu sein.
-/
#check Finset.range

/- Beachte: im folgenden Lemma wird die *Division natürlicher Zahlen* verwendet.

Da das Ergebnis einer Division auf den natürlichen Zahlen eine natürliche Zahl sein muss,
ist `a / b` das abgerundete Ergebnis der entsprechenden Division.

Dies macht es schwieriger, Aussagen darüber zeigen, weshalb wir diese Operation i.A. vermeiden. -/

example (n : ℕ) : ∑ i ∈ (range (n + 1)), (i : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    norm_cast
    -- Die Taktik `norm_cast` schiebt Type-Castings herum.
    ring

/- Wir können Aussagen über die natürlichen Zahlen auch mit anderen Induktionsprinzipien lösen: -/

/- Unsere Induktionsannahme im folgenden Induktionsprinzip ist nicht
"für ein beliebiges, aber festes `n` gilt `P(n)`", sondern
"Für ein beliebiges, aber festes `n` gilt `P(m)` für alle `m ≤ n`" -/
#check Nat.le_induction

/- Zwei Induktionsvoraussetzungen (`P(0)` und `P(1)`) und im Induktionsschritt schließend wir von
`P(n)` und `P(n+1)` auf `P(n+2)`. -/
#check Nat.twoStepInduction

/- We can use other induction principles with `induction ... using ... with` -/

theorem fac_dvd_fac (n m : ℕ)
    (h : n ≤ m) : fac n ∣ fac m := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [fac]
    exact Dvd.dvd.mul_left ih (k + 1)

/- Die folgende Aussage definiert die Fibonacci-Folge: -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- # Aufgaben -/

/- Zeige die folgenden Aussagen mit vollständiger Induktion: -/

/- `F_1 + F_3 + ... + F_{2 * (n - 1) + 1} = F_{2 * n}` -/
example (n : ℕ) : ∑ i ∈ range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by
  sorry

/- `F_1 + F_2 + ... + F_{n-1} = F_{n+2}` -> Als Beispiel zeigen! -/
example (n : ℕ) : ∑ i ∈ range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by
  sorry

/- Die Summe der Quadratzahlen bis `n^2` ist `n * (n + 1)  (2 * n + 1) / 6`. -/
example (n : ℕ) : 6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry

/- Für alle natürlichen Zahlen `n` gilt `2^n ≤ (n + 1)!` -/
theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by
  sorry

/- `n! = 1 * 2 * ... * n` -/
example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  sorry

/- *Gauß'sche Summenformel* : Die Summe der natürlichen Zahlen `≤ n` ist `n * (n + 1)/2`. -/
lemma gauss : ∀ (m : ℕ), (∑ i ∈ range (m + 1), (i : ℚ) = m * (m + 1) / 2) := by
  sorry

/- `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ range (n + 1), (i : ℚ)) ^ 2 := by
  sorry

/- `(2 * n)! = n! * 2^n * (Produkt der ungeraden Zahlen < 2 * n)` -/
example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i ∈ range n, (2 * i + 1) := by
  sorry

#min_imports
