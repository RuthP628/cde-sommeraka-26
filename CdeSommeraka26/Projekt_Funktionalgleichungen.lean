import Mathlib

set_option linter.style.whitespace false

/- # Funktionalgleichungen formalisieren

Formalisiere die folgenden Funktionalgleichungen.

Die Aufgaben sind nicht nach Schwierigkeit sortiert und weitestgehend unabhängig voneinander
(bis auf die Cauchy-Funktionalgleichungen. Diese bauen aufeinander auf.
Außerdem benötigen einige der Aufgaben (wenn auch nicht alle) irgendeine Form der Cauchy-
Funktionalgleichung. Du kannst diese allerdings auch nur staten und dann blackboxen).

Starte gerne mit der Funktionalgleichung, die dir am besten gefällt.

-/

/- # Wo finde ich Beweise in natürlicher Sprache?

Lösungen von Integer Cauchy, Rational Cauchy, Cauchy für stetige Funktionen,
Jensen, DURR WE WANT STUFF TO CANCEL und Kyrgyzstan sind im frei zugänglichen pdf
"Introduction to Functional Equations" von Evan Chen zu finden
(https://web.evanchen.cc/handouts/FuncEq-Intro/FuncEq-Intro.pdf).

Die Lösung für IMO 2019 / P1 ist in der IMO-Shortlist von 2019 zu finden
(Siehe https://www.imo-official.org/).

Für die Lösungen von 601016 und der Aufgabe aus dem MBL-QQ könnt ihr mich gerne ansprechen.

 -/

/- **Integer Cauchy**

Zeige: Wenn eine Funktion `f : ℤ → ℤ` die Funktionalgleichung `f (a + b) = f a + f b` für alle
`a, b ∈ ℤ` erfüllt, dann ist sie linear mit konstantem Term `0`.

-/

/- **Cauchy-Funktionalgleichung auf ℚ**

Achtung: diese Aufgabe ist deutlich schwieriger als die Wettbewerbsaufgaben
und macht mMn auch weniger Spaß.

Zeige: Wenn eine Funktion `f : ℚ → ℚ` die Funktionalgleichung `f (a + b) = f a + f b`
für alle `a, b ∈ ℤ` erfüllt, dann ist sie linear mit konstantem Term `0`.

Die folgenden Lemmata beschreiben "Induktion" auf den Rationalen Zahlen und könnten nützlich sein:
-/

#check Rat.numDenCasesOn
#check Rat.numDenCasesOn'
#check Rat.numDenCasesOn''

/- **Cauchy-Funktionalgleichung für stetige Funktionen `ℝ → ℝ`**

Achtung: Diese Aufgabe ist ziemlich anders als die Wettbewerbsaufgaben und benötigt mehr Theorie.

Zeige: Wenn eine stetige Funktion `f : ℝ → ℝ` die Funktionalgleichung `f (a + b) = f a + f b`
erfüllt, dann ist sie linear mit konstantem Term `0`.

-/

/- **Aufgabe 601016 der deutschen Mathematik-Olympiade**

Finde alle Funktionen `f : ℝ × ℝ → ℝ`
mit der Eigenschaft `∀ a b c, a + f (b, c) = f (a, b) + f (a, c)`
und zeige, dass es keine weiteren gibt.

-/

/- **Jensen's Funktionalgleichung**

Zeige, dass die Funktionalgleichung `f x + f y = 2 * f ((x + y) / 2)` über `ℝ`
genau von linearen Funktionen gelöst wird.

Tipp: definiere eine Hilfsfunktion und zeige, dass diese Cauchy erfüllt.

-/

/- **DURR WE WANT STUFF TO CANCEL**

Finde alle Funktionen `f : ℝ → ℝ` mit der Eigenschaft
`f (x^2 + y) = f (x^(27) + 2y) + f (x^4)` und zeige, dass es keine weiteren gibt.

-/

/- **IMO 2019 / P1**

Finde alle Funktionen `f : ℤ → ℤ` mit der Eigenschaft, dass `f (f (m+n)) = f (2 * n) + 2 * f m`
für alle `m, n ∈ ℤ` gilt.

-/

/- **Kyrgyzstan 2012**

Finde alle Funktionen `f : ℝ → ℝ` so dass für alle `x, y ∈ ℝ` gilt:
`f ((f x)^2 + f y) = x (f x) + y` und zeige, dass es keine weiteren solchen Funktionen gibt.

-/

/- **MBL-B 2024 Qualifying Quiz**

Sei `f : ℤ_{> 0} → ℤ_{> 0}` eine Funktion,
so dass `f (n + (f n)) * (n + (f m)) = (f (2 m) + 2 (f n)) * (f n)` gilt.

Bestimme `f (2026)`.

Tipp: Definiere `f` als eine Funktion `ℤ → ℤ`,
die positive ganze Zahlen auf positive ganze Zahlen abbildet
und nur für `m, n > 0` die obige Eigenschaft erfüllt, um Typecasting zu vermeiden.

-/
