# Lean-Kurs auf der CdE-SommerAkademie 2026

In diesem Lean-Projekt findet ihr alle Materialien für den Lean-Kurs auf der CdE-SommerAkademie 2026.

Um lokal an diesem Projekt zu arbeiten, führe die folgenden Schritte aus:

1. Öffne den Folder auf deinem Computer, in dem du dieses Projekt als Subfolder haben möchtest, im Terminal auf deinem Computer.

2. Gib nun den folgenden Command im Terminal ein:
  ```
   git clone https://github.com/RuthP628/cde-sommeraka-26
```

3. Nun sollte dein Computer eigenständig einen Ordner namens cde-sommeraka-26 erstellt haben. Navigiere nun mithilfe des folgenden Commands in diesen Ordner:
   ```
   cd cde-sommeraka-26
   ```

4. Gib nun den folgenden Code im Terminal ein:
   ```
   lake exe cache get
   ```

5. Öffne nun den Folder cde-sommeraka-26 (NICHT einen der Subfolder dieses Folders) mit VS Code

6. Jetzt sollte alles geklappt haben. Wenn du überprüfen willst, ob alles läuft wie geplant, ersetze den Code in scratchfile.lean durch die folgenden Zeilen:

   ```
   import Mathlib.Topology.Basic

   #check TopologicalSpace
   ```

7. Wenn Du Syntax Highlighting siehst und hinter dem #check blauer Text angezeigt wird, hast du alles richtig gemacht!
