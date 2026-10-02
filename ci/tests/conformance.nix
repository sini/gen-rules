# ADR-0035 CONFORMANCE, POSITION-SCOPED, OVER THE WHOLE TREE. No framework or fleet word sits at a
# KIND, LABEL, OPTION or ERROR position anywhere in this library's text. The two positions asserted
# are the two that ARE vocabulary:
#
#   (1) a double-quoted string that IS the word        (kind, label, error text)
#   (2) the word at binding position at line start     (option, attribute, kind key)
#
# Comments are stripped first: a comment is none of those positions, and documentation must be able
# to name what it excludes. The word list is one pipe-joined string split at runtime, so this file
# does not satisfy predicate (1) against itself.
{ lib, ... }:
let
  root = ../..;
  forbidden = lib.splitString "|" "host|user|system|machine|service|cluster|server|network|port|interface|datacenter";
  skip = [
    ".git"
    ".direnv"
    "result"
    ".worktrees"
    ".gcroots"
  ];

  filesUnder =
    dir: prefix:
    builtins.concatLists (
      lib.mapAttrsToList (
        name: type:
        if type == "directory" then
          (if builtins.elem name skip then [ ] else filesUnder (dir + "/${name}") "${prefix}${name}/")
        else if type == "regular" then
          [
            {
              name = "${prefix}${name}";
              text = builtins.readFile (dir + "/${name}");
            }
          ]
        else
          [ ]
      ) (builtins.readDir dir)
    );
  sources = builtins.filter (s: lib.hasSuffix ".nix" s.name) (filesUnder root "");

  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );
  lines = builtins.concatMap (
    src:
    map (l: {
      inherit (src) name;
      line = l;
    }) (lib.splitString "\n" (stripComments src.text))
  ) sources;

  atPosition =
    words: l:
    builtins.any (
      w:
      builtins.match ".*\"${w}\".*" l != null
      || builtins.match "[[:space:]]*${w}[[:space:]]*=.*" l != null
    ) words;
  hits = words: map (x: "${x.name}: ${x.line}") (builtins.filter (x: atPosition words x.line) lines);
in
{
  flake.tests.conformance = {
    test-no-fleet-vocabulary-at-kind-label-option-or-error-position = {
      expr = hits forbidden;
      expected = [ ];
    };

    # ★ THE CONTROL: the same predicate, same run, over this library's own invented vocabulary, which
    # does sit at those positions. If it reads 0 the scanner is broken and the zero above means nothing.
    test-positive-control-own-vocabulary-is-found = {
      expr =
        builtins.length (hits [
          "tuck"
          "thimble"
        ]) > 0;
      expected = true;
    };

    # The domain, so a zero is not "the walk found no files".
    test-the-scan-reached-the-library-and-the-cells = {
      expr = builtins.all (n: builtins.any (s: s.name == n) sources) [
        "lib/apply.nix"
        "lib/walk.nix"
        "ci/tests/door.nix"
        "ci/tests/_fixtures/world.nix"
      ];
      expected = true;
    };
  };
}
