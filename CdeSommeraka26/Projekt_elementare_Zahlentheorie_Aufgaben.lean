import Mathlib

/- # Quadratzahlen abschätzen

Zeige, dass für positive ganze Zahlen `a` und `b` immer mindestens eine der Zahlen
`a^2 + b` und `b^2 + a` keine Quadratzahl ist.

Verwende für die Formulierung der Aussage die Proposition `IsSquare`.

Tipp 1: Zeige zunächst, dass unter den Annahmen `a ≤ b` und `a^2 + b = n^2`
        sowohl `b < n` als auch `b > n` gelten müsste.

Tipp 2: Versuche, Type Casts zu vermeiden!

-/

#check IsSquare

/- # Primzahlen und Zweierpotenzen

Zeige, dass, wenn für `n : ℕ` `2^n - 1` eine Primzahl ist, schon `n` eine Primzahl sein muss.

Zeige dazu zunächst, dass eine natürliche Zahl `n` genau dann keine Primzahl ist,
wenn `n = 0` oder `n = 1` gilt oder wenn `a, b : ℕ` mit `a ≥ 2` und `b ≥ 2` existieren, so dass
`n = a * b` gilt.

Tipp: Zeige das finale Ziel zunächst auf Papier.

Die folgenden Lemmata könnten nützlich sein:

-/

#check Nat.prime_def_lt
#check Nat.prime_def_lt'
#check Nat.le_one_iff_eq_zero_or_eq_one
#check Nat.succ_le

/- # Kleiner Satz von Fermat

Zeige, dass für alle natürlichen Zahlen `a` und Primzahlen `p`
`a^p - a` durch `p` teilbar ist.

Tipp: Zeige die Aussage mit Induktion und versuche, ein Lemma in Mathlib zu finden,
das Potenzen auflöst.

Die Websites https://loogle.lean-lang.org, https://leansearch.net und https://leandex.projectnumina.ai
könnten dabei hilfreich sein.

-/
