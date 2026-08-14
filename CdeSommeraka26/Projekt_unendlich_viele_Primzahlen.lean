import Mathlib

set_option linter.style.whitespace false

/- # Unendlich viele Primzahlen

Das Ziel dieses Projekts ist es, zu zeigen,
dass es unendlich viele Primzahlen gibt.

Wenn du noch Zeit hast, kannst du den Beweis verallgemeinern, indem du zeigst,
dass es unendlich viele Primzahlen gibt, die kongruent zu 3 modulo 4 sind.

-/

#check Nat.Prime

/- **Schritt 1**

Zeige, dass jede natürliche Zahl `m`, die nicht `0` oder `1` ist, größer oder gleich `2` ist.

Tipp: `cases`/ `induction` und das folgende Lemma könnten nützlich sein:

-/

#check Nat.succ_le_succ

/- **Schritt 2**

Zeige nun mittels starker Induktion auf den natürlichen Zahlen, dass für alle `n ≥ 2`
eine Primzahl `p` existiert, die `n` teilt.

Verwende NICHT das Lemma `Nat.exists_prime_and_dvd` aus mathlib.

Die folgenden nützlichen Lemmata darfst du verwenden:

-/

#check Nat.prime_def_lt
#check zero_dvd_iff

/- **Schritt 3**

Zeige nun, dass für alle natürlichen Zahlen `n : ℕ` eine Primzahl `p > n` existiert,
indem du verwendest, dass `n! + 1` einen Primteiler besitzt.

In mathlib bezeichnet `Nat.factorial n` die Fakultät von `n`.
Die folgenden Lemmata könnten nützlich sein:

-/

#check Nat.factorial_pos
#check Nat.dvd_factorial
#check Nat.dvd_sub


/- Wir wollen nun zeigen, dass für jede endliche Menge natürlicher Zahlen
eine Primzahl `p` existiert, die nicht in der endlichen Menge enthalten ist.-/

open Finset BigOperators

/- **Schritt 5**

Zeige nun die folgende Aussage:

  Sei `s` eine endliche Menge natürlicher Zahlen, so dass jedes Element von `s` prim ist,
  sei außerdem `p` prim und das Produkt der Zahlen in `s` sei durch `p` teilbar.
  Dann ist `p` in `s`.

Das Produkt aller Elemente in einer endlichen Menge `s` wird in Lean notiert als `Π i ∈ s, i`.

Die folgenden Lemmata könnten ebenfalls nützlich sein:
-/

#check Finset.dvd_prod_of_mem
#check Nat.Prime.eq_one_or_self_of_dvd

/- **Schritt 6**

Die endliche Menge aller Elemente `x` eines Finsets `s`, für die eine bestimmte Aussage `P x` gilt,
wird in Lean als `s.filter P` geschrieben. Dies ist das Analogon zu `{x ∈ S | P x}`
für endliche Mengen (Finsets).

Zeige nun, dass für jede Menge natürlicher Zahlen eine Primzahl `p` existiert, die
nicht in der endlichen Menge enthalten ist.

Die folgenden Lemmata könnten nützlich sein:
-/

#check mem_filter
#check Finset.prod_pos
#check Nat.dvd_sub

/- **Verallgemeinerung: Primzahlen kongruent 3 mod 4**

Zeige, dass es unendlich viele Primzahlen kongruent zu 3 mod 4 gibt.

Die Aussage "n ist kongruent zu 3 mod 4" ist in Lean formalisiert als `n % 4 = 3`.

Folge dazu den folgenden Schritten:

1.) Aus `n * m % 4 = 3` folgt `n % 4 = 3` oder `m % 4 = 3`.

2.) Für alle `n` mit `n % 4 = 3` gilt `n ≥ 2`.

3.) Wenn `n % 4 = 3` gilt, hat `n` einen Primfaktor, der kongruent zu 3 mod 4 ist.

4.) Für alle natürlichen Zahlen `n` gibt es eine Primzahl `p > n` mit `p % 4 = 3`.

-/
