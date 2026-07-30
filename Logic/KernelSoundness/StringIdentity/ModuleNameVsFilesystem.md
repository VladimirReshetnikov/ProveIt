# Module names vs the filesystem

Lean's module identity is byte-exact on `Name`. The filesystem's is not:
NTFS and APFS/HFS+ are case-insensitive by default, and HFS+ additionally
normalises names to NFD.

Reproduce (Windows or macOS):

```bash
printf 'def secret : Nat := 1
' > Foo.lean
lean -o Foo.olean Foo.lean
LEAN_PATH=. lean <<< 'import FOO
#eval secret'
```

Observed on Windows/NTFS, Lean 4.32.0:

* `import FOO` **succeeds** and evaluates `secret` to `1` -- the module actually
  loaded is `Foo`, which is not the name written in the source.
* `import Foo` followed by `import FOO` is caught:
  `import FOO failed, environment already contains 'secret' from Foo`.

So the collision is *detected* when both spellings appear, but a single
mis-cased import silently resolves to a different module than the one named.
An audit that decides "does this file import only trusted modules?" by matching
the import strings can therefore be given a name that is not the module loaded.

The same applies across platforms: a repository authored on a case-sensitive
filesystem may legitimately contain `Foo.lean` and `FOO.lean` as two distinct
modules; checked out on Windows or macOS they collide into one file.
