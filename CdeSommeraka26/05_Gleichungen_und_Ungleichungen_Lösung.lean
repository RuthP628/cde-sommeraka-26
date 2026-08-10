import Mathlib

open Real Nat

/-! ## Gleichungen und Ungleichungen mit calc beweisen ##-/

variable {a b c d e x y z : ℝ}

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- Wir können diese Lemmata manuell anwenden
oder die Taktiken `rfl`/`trans`/`calc` nutzen: -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl

/- Die `calc`-Umgebung erlaubt es, Gleichungs- und Ungleichungsketten
wie auf Papier hinzuschreiben und dabei jedes Gleichheitszeichen zu beweisen.

Dies macht den Code deutlich lesbarer für Menschen. Ich würde empfehlen,
wenn möglich immer `calc`-Umgebungen zu verwenden, auch wenn jeder `calc`-Beweis
auch ausschließlich mit den Taktiken geführt werden kann, die wir bislang gesehen haben. -/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  calc a
      = b := h₀
    _ < c := h₁
    _ ≤ d := h₂
    _ < e := h₃

/- Mit der Taktik `trans` können wir Ungleichungen beweisen, indem wir einen Term angeben,
von dem wir behaupten, dass er zwischen den beiden Termen, deren Ungleichung wir zeigen wollen,
liegt.

Ebenso wie `constructor` trennt `trans` ein Ziel in mehrere unabhängige Ziele auf.
-/

example (h : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  trans b
  · assumption
  · assumption

/- `linarith` kann Gleichungen und Ungleichungen,
die eine Linearkombination der Annahmen sind, direkt beweisen. -/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (x y z : ℝ) (hx : x ≤ 3 * y) (h2 : ¬ y > 2 * z)
    (h3 : x ≥ 6 * z) : x = 3 * y := by
  linarith


/- Mathlib enthält eine Reihe von nützlichen Lemmata,
die Monotonie wichtiger Funktionen zeigen.
Hier sind einige Beispiele: -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a)

/- Die Taktik `gcongr` wendet diese Lemmata automatisiert auf Ungleichungen an: -/

example (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by
  gcongr
  linarith

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by
  gcongr
  linarith

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  gcongr

/- `congr` ist das Äquivalent zu `gcongr` für Gleichungen. -/

example (h : a = b) : c - exp b = c - exp a := by
  congr
  symm
  exact h

/- **Aufgaben:** -/

/-- Zeige die folgende Aussage: -/
example (a b c : ℝ) : a + b ≤ c → a ≤ c - b := by
  intro h
  linarith


/- Hinweis: für reine Rechenaufgaben kann man `norm_num` verwenden
(auch wenn `ring` und `linarith` in einigen solchen Fällen auch funktionieren). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- Zeige die folgende Aussage mit `calc`. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
  y = y + 2 * x - 2 * x := by ring
  _ ≥ 3 - 2 * x := by linarith
  _ ≥ 3 - 2 * (2 - 3) := by linarith
  _ > 3 := by norm_num

/-- In manchen Fällen kann es nützlich sein,
in Beweisen mit `gcongr` ein `+ 0` hinzuzufügen -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
  n = n + 0 := by ring
  _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Manchmal geht `congr`/`gcongr` zu weit in einen Term hinein.
In diesen Fällen kann man `gcongr` Patterns vorgeben.
Wenn das Pattern `?_` enthält, wird automatisch ein weiteres Ziel erzeugt.

Um dieses Vorgehen bei `congr` anzuwenden, muss man `congrm` verwenden. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  have h : m^2 ≥ 0 := by exact sq_nonneg m
  calc
  n - m^2 ≤ n - 0 := by linarith
  _ ≤ n + 3 := by linarith



example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by
    gcongr ?_ +1
    have h₆: (a₃ ≤ b₃ - 2) := by linarith
    have h₇: (exp (a₁ + a₂) ≤ exp (b₁ + b₂)) := by
      norm_num
      linarith
    linarith

/-- `calc` funktioniert auch mit der Teilbarkeitsrelation statt mit Gleichheitszeichen.
Zeige die folgende Aussage mit `calc`. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by
  calc
  n ∣ m := by exact h₁
  _ = k := by exact h₂
  _ ∣ l := by exact h₃

/-
`(n)!` steht für die Fakultät auf den natürlichen Zahlen.
Die Klammern sind beim eingeben notwendig.
Zeige die folgende Aussage mit `calc`.

Du kannst `exact?` verwenden, um Lemmata in mathlib zu finden,
z.B. die Aussage, dass die Fakultät monoton ist.

Beachte: `(n+1)!` ist in Lean definiert als `(n+1) * (n)!`.
Insbesondere wird `(n)! * (n+1)` nicht als die Definition von `(n + 1)!` erkannt.-/

example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  calc
  (n)! ∣ (m)! := by exact factorial_dvd_factorial h
  _ ∣ (m + 1) * (m)! := by exact Nat.dvd_mul_left m ! (m + 1)
  _ = (m + 1)! := by exact Eq.symm (factorial_succ m)
