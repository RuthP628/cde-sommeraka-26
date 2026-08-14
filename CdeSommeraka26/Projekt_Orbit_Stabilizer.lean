import Mathlib

set_option linter.style.whitespace false

/- # Orbit-Stabilizer-Theorem

Ziel: Beweise das Orbit-Stabilizer-Theorem,
d.h. konstruiere eine Bijektion zwischen den Nebenklassen des Stabilizers einer Gruppenwirkung
und dem Orbit derselben Gruppenwirkung.
 -/

/- **Gruppenwirkungen**
Definiere deine eigene Klasse `MyGroup`, die eine Gruppe beschreibt.

Definiere Untergruppen und Nebenklassen.

Definiere außerdem Wirkungen von Gruppen (nach deiner Definition) auf anderen Typen.
-/

/- **Orbit und Stabilizer**

Definiere für ein `x : α` den *Stabilizer von x* als die Menge der Elemente aus `G`,
die `x` konstant lassen. Zeige, dass der Stabilizer von `x` eine Untergruppe von `G` ist.

Definiere außerdem den *Orbit von x* als die Menge der Elemente `y : α`, für die es ein `g : G`
gibt mit `g * x = y`.

-/

/- **Orbit-Stabilizer Theorem**

Konstruiere eine Bijektion zwischen dem Orbit von `x` und den Nebenklassen des Stabilizers von `x`.
-/
