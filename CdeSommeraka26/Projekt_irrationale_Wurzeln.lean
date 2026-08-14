import Mathlib

set_option linter.style.whitespace false

/- # Wurzeln von Primzahlen sind irrational -/

/-  Betrachte die folgenden zahlentheoretischen Aussagen: -/

/- Eine natürliche Zahl ist genau dann eine Primzahl, wenn sie mindestens `2` ist
und aus `m | p` und `m < p` schon `m = 1` folgt. -/
#check Nat.prime_def_lt

/- Wenn eine natürliche Zahl `p` eine Primzahl ist, folgt für natürliche Zahlen `m`
aus `m | p` schon `m = 1 ∨ m = p`. -/
#check Nat.Prime.eq_one_or_self_of_dvd

/- `2` und `3` sind Primzahlen. -/
#check Nat.prime_two
#check Nat.prime_three

/- Eine Primzahl `p` in den natürlichen Zahlen teilt genau dann `m * n`,
wenn sie `m` oder `n` teilt. -/
#check Nat.Prime.dvd_mul

/- Eine Primzahl `p` in den natürlichen Zahlen teilt genau dann `m^n`, wenn sie `m` teilt. -/
#check Nat.Prime.dvd_of_dvd_pow

/- **Aufgabe 1**

Zeige, dass aus `2 | m^2` schon `2 | m` folgt.
-/

/- Zwei natürliche Zahlen sind genau dann teilerfremd,
wenn ihr größter gemeinsamen Teiler `1` ist.-/
#print Nat.Coprime

/- `a | b` gilt genau dann, wenn ein `c : ℕ` existiert mit `b = c * a`. -/
#check dvd_iff_exists_eq_mul_left

/- **Aufgabe 2**

Zeige, dass für teilerfremde `m` und `n` immer `m^2 ≠ 2 * n^2` gilt.

Verallgemeinere dies: Zeige, dass `m` und `n` immer `m^2 ≠ p * n^2` gilt.
-/

#check ℚ

/- **Aufgabe 3**

Nimm nun an, es gäbe eine rationale Zahl `q` mit `q^2 = p`.

Nutze die Definition der Struktur `Rat` der rationalen Zahlen, um zu zeigen,
dass es dann zwei ganze Zahlen `m` und `n` geben müsste, für die `m^2 = p * n^2` gelten müsste,
und führe dies zum Widerspruch.

-/
