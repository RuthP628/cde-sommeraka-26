import Mathlib

set_option linter.style.whitespace false

open Real Function Set

noncomputable section

/-
# Structures und Classes

In Lean können wir neue (dependent) types, genannt structures,
definieren, um Daten und ihre Eigenschaften zusammen zu bündeln.

Bspw. bündelt die folgende Struktur `Point` drei Koordinaten:
-/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point

section

/- Für ein Objekt `a` vom Typ `Point` erhalten wir nun die Projektionen
auf die einzelnen Koordinaten: -/
variable (a : Point)
#check a.x
#check a.y
#check a.z
#check Point.x a

example : a.x = Point.x a := by rfl

end

/- Das Attribut `@[ext]` oben erlaubt uns, die Taktik `ext` zu nutzen,
um zu zeigen, dass zwei Punkte gleich sind: -/

example (a b : Point)
    (hx : a.x = b.x)
    (hy : a.y = b.y)
    (hz : a.z = b.z) :
    a = b := by
  ext
  all_goals assumption

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext <;> assumption

#check Point.ext_iff

/- Es gibt mehrere Wege, um spezifische Objekte vom Typ `Point`
(oder generell Instanzen von einer Structure) zu definieren:

Tipp: Wenn ihr die Syntax vergessen habt, könnt ihr auch erst einmal
`def myPoint : Point := sorry` schreiben.

Wenn ihr dann euren Cursor vor das `sorry` bewegt,
erscheint eine blaue Glühbirne💡.
Auf diese könnt ihr klicken, um das Grundgerüst einer Definition zu erhalten. -/

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 :=
  { x := 1, y := 2, z := 3 : Point }

def myPoint3 : Point :=
 id {
   x := 1
   y := 2
   z := 3
 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3

namespace Point

/- Wir können Operationen auf Punkten definieren, wie z.B. Addition.

Die folgenden drei Definitionen sind alle äquivalent.-/

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

def add'' : Point → Point → Point
  | ⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩ => ⟨ux + vx, uy + vy, uz + vz⟩

/- Wichtig: Wir haben diese Operationen im `namespace Point` definiert.
D.h. innerhalb dieses namespaces können wir `add p q` schreiben, um zwei Punkte zu addieren.
Außerhalb des namespaces müssen wir dagegen `Point.add p q` schreiben.

In jedem Fall können wir *Projektions-Notation* verwenden,
d.h. `p.add q` where `p q : Point`.
Auch außerhalb des namespaces `Point` versteht Lean dann, dass `Point.add` gemeint ist,
da `p` den Typ `Point` hat. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2
#check (myPoint1.add myPoint2).1
#eval (myPoint1.add myPoint2).1

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/- Um namespaces zu öffnen, verwenden wir das Keyword `open`: -/
open Point

#check add myPoint1 myPoint2

namespace Point

/- Nun können wir Eigenschaften von Punkten zeigen.
Das Keyword `protected` im untenstehenden Lemma bedeutet, dass wir immer
(insbesondere auch im namespace `Point`)`Point.add_comm`
schreiben müssen, um auf das Lemma zuzugreifen. -/

protected lemma add_comm (a b : Point) :
  add a b = add b a := by simp [add, add_comm]

#check Point.add_comm

/- Wir können `Point.add` als Instanz der "normalen" Addition `add`
betrachten, um `Point.add` mit der Notation `+` zu schreiben.

Wir werden später noch sehen, was das `instance`-keyword im Detail tut.. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by {
  ext
  all_goals simp [add_comm]
  }

/- **Aufgabe**.
Definiere Skalarmultiplikation einer reellen Zahl mit einem `Point` -/

end Point

/- **Aufgabe**

Definiere die structure `PythagoreanTriple'`, d.h.
Tripel `a b c : ℕ` mit `a^2 + b^2 = c^2`.

Gib ein Beispiel eines pythagoräischen Tripels an
und zeige, dass Multiplikation eines pythagoräischen Tripels mit einer
konstanten natürlichen Zahl ein weiteres pythagoräisches Tripel liefert.
-/

/- **Aufgabe**.
Definiere die Struktur der "strikt bipunktierten Typen", d.h. einen Typen
zusammen mit 2 verschiedenen Punkten `x₀ ≠ x₂`.

State und beweise außerdem das Lemma,
dass für die Komponenten `x₀` und `x₁` eines beliebigen Elements `a`
eines strikt bipunktierten Typen gilt:
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

/- Betrachte nun die folgende Struktur: -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PosPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by
    apply add_pos
    · exact a.x_pos
    · exact b.x_pos
  y_pos := by linarith [a.y_pos, b.y_pos]
  z_pos := by linarith [a.z_pos, b.z_pos] }

/- Probleme mit den obigen Definitionen:

* Doppelter Code, um `PosPoint` und `Point` sowie die Addition zu definieren
* Wir wollen nicht von jeder Instanz von `PosPoint` extra zeigen müssen,
  dass sie auch eine Instanz von `Point` ist.

Dies wäre noch nerviger, wenn wir Monoide, Gruppen, Ringe und Körper auf diese Art
definieren würden.

Aus diesem Grund können wir Strukturen wie `Point` erweitern:-/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint'.toPoint

def PosPoint'.add (a b : PosPoint') : PosPoint' :=
{ a.toPoint + b.toPoint with
  x_pos := by simp; linarith [a.x_pos, b.x_pos]
  y_pos := by simp; linarith [a.y_pos, b.y_pos]
  z_pos := by simp; linarith [a.z_pos, b.z_pos] }

/- Für die obige Situation können wir auch Subtypen verwenden.

Die Notation für Subtypen ist ähnlich zur Notation für Mengen,
aber wir schreiben `{x : α // p x}` anstelle von `{x : α | p x}`. -/

structure PosReal' where
  toReal : ℝ
  toReal_pos : toReal > 0


def PosReal : Type :=
  { x : ℝ // x > 0 }

def set_of_positive_reals : Set ℝ :=
  { x : ℝ | x > 0 }

/- Dieser Ansatz gibt uns allerdings nicht automatisch sinnvolle Namen für die Projektionen.
Dementsprechend wird es hässlich, sobald wir mehr als zwei Projektionen haben:. -/

example (x : PosReal) : x.1 > 0 := x.2
example (x : PosReal') : x.1 > 0 := x.2

def PosPoint'' : Type :=
  { x : ℝ × (ℝ × ℝ) // x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0 }


/- Structures können von Parametern abhängen (→ dependent types!) -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk cos sin tan


/- # Abelsche Gruppen
Wir definieren Abelsche Gruppen in Lean: -/

structure AbelianGroup where
  G : Type*
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg (x : G) : G
  add_neg : ∀ x : G, add x (neg x) = zero

def IntGroup : AbelianGroup where
  G := ℤ
  add a b := a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg a := -a
  add_neg := Int.add_right_neg

lemma AbelianGroup.zero_add (g : AbelianGroup) (x : g.G) :
    g.add g.zero x = x := by
  rw [g.comm, g.add_zero]


/-
Probleme mit diesem Ansatz:
* Die Notation `AbelianGroup.add` und `AbelianGroup.neg` erscheint nicht sinnvoll.
* Wir wollen, dass `ℤ` direkt die Information trägt, eine abelsche Gruppe zu sein.
* Wir wollen, dass Lean weiß, dass `G × G` abelsche Gruppe ist, wenn `G` eine abelsche Gruppe ist.

Indem man das keyword `class` anstelle von `structure` verwendet,
erstellt Lean eine Database von "instances" dieser Klasse.

Das Keyword `instance` erlaubt uns, Elemente zu dieser Database hinzuzufügen.
-/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

instance some_name : AbelianGroup' ℤ where
  add := fun a b ↦ a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact?

#eval AbelianGroup'.add (2 : ℤ) (5 : ℤ)

infixl:65 " +' " => AbelianGroup'.add

#check 2 + 3 * 5
#eval (-2) +' 5

notation " 𝟘 " => AbelianGroup'.zero


prefix:max "-'" => AbelianGroup'.neg

/- Um anzunehmen, dass ein Objekt zu einer bestimmten Klasse gehört,
schreiben wir dieses in den Annahmen in eckige Klammern.

Diese Argumente heißen *instance-implicit arguments*.
Wenn wir ein Lemma mit instance-implicit arguments anwenden, sucht
Lean automatisch nach einem passenden Eintrag in der `instance`-Database.
-/

#check AbelianGroup'.add

instance AbelianGroup'.prod (G G' : Type*) [AbelianGroup' G] [AbelianGroup' G'] :
    AbelianGroup' (G × G') where
  add a b := (a.1 +' b.1, a.2 +' b.2)
  comm a b := by ext <;> apply AbelianGroup'.comm
  assoc a b c := by ext <;> apply AbelianGroup'.assoc
  zero := (𝟘, 𝟘)
  add_zero a := by ext <;> apply AbelianGroup'.add_zero
  neg a := (-' a.1, -' a.2)
  add_neg a := by ext <;> apply AbelianGroup'.add_neg

/- Now Lean will figure out itself that `AbelianGroup' (ℤ × ℤ)`. -/
set_option trace.Meta.synthInstance true in
#check ((2, 3) : ℤ × ℤ) +' (4, 5)

set_option trace.Meta.synthInstance true in
#synth AbelianGroup' (ℤ × ℤ)

#check mul_comm

/- **Aufgabe**

Zeige, dass wenn `G` eine abelsche Gruppe ist,
dann auch die Menge der Tripel aus Elementen von `G` eine abelsche Gruppe ist. -/

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry

#min_imports
