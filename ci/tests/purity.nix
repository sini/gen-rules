# PURITY INVARIANT — the library source reaches NO nixpkgs `lib`. The module-system vocabulary the
# registration table needs (`mkOption`, `mkMerge`, `lazyAttrsOf`, `raw`) is gen-merge's, reached as
# `merge.<name>`; a bare or `lib.`-qualified spelling of it is the nixpkgs one.
#
# Scope: `lib/**.nix` + the root `flake.nix` and `default.nix`. NOT `ci/` — the harness legitimately
# uses nixpkgs `lib`, including to run this scan.
{ genPrelude, lib, ... }:
let
  libDir = ../../lib;

  # Comment-stripped source, so documentation may NAME a forbidden token.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # The strip's premise, asserted: the `#` it cuts at stands OUTSIDE a string literal.
  countQuotes = s: (lib.length (lib.splitString "\"" s)) - 1;
  cutIsInString =
    line:
    let
      kept = stripComments line;
    in
    kept != line && lib.mod (countQuotes kept) 2 == 1;

  sources =
    map (name: {
      name = "lib/${name}";
      text = builtins.readFile (libDir + "/${name}");
    }) (builtins.filter (lib.hasSuffix ".nix") (builtins.attrNames (builtins.readDir libDir)))
    ++ [
      {
        name = "flake.nix";
        text = builtins.readFile ../../flake.nix;
      }
      {
        name = "default.nix";
        text = builtins.readFile ../../default.nix;
      }
    ];

  premiseBreaches = builtins.concatMap (
    src:
    lib.concatLists (
      lib.imap1 (i: line: lib.optional (cutIsInString line) "${src.name}:${toString i}") (
        lib.splitString "\n" src.text
      )
    )
  ) sources;

  libSources = builtins.filter (s: lib.hasPrefix "lib/" s.name) sources;
  xmlCalls = srcs: lib.foldl' (n: s: n + lib.length (lib.splitString "toXML" s.text) - 1) 0 srcs;

  forbidden = [
    "nixpkgs"
    "lib."
    "evalModules"
  ];

  scan =
    srcs:
    builtins.concatMap (
      src:
      builtins.concatMap (
        tok: lib.optional (genPrelude.hasInfix tok src.text) "${src.name}: ${tok}"
      ) forbidden
    ) srcs;
in
{
  flake.tests.purity = {
    test-the-comment-strip-never-cut-inside-a-string = {
      expr = premiseBreaches;
      expected = [ ];
    };

    test-the-library-source-reaches-no-nixpkgs = {
      expr = scan (map (s: s // { text = stripComments s.text; }) sources);
      expected = [ ];
    };

    # ★ THE CONTROL: the same predicate over the UNSTRIPPED source, whose comments name the tokens.
    # A scan reading 0 on both would be a broken predicate rather than a pure library.
    test-positive-control-the-unstripped-source-carries-the-tokens = {
      expr = builtins.length (scan sources) > 0;
      expected = true;
    };

    # gen's one `builtins.toXML` reading is gen-prelude's `patternOf` (den-hoag-a48xt arm (a)); this
    # library reads the pattern through it and calls `toXML` nowhere (den-hoag-gtwxg gate C4).
    test-the-library-calls-no-toxml = {
      expr = xmlCalls (map (s: s // { text = stripComments s.text; }) libSources);
      expected = 0;
    };

    # ★ THE CONTROL: the unstripped library names `toXML` in the comment that points at the reader.
    test-positive-control-the-unstripped-library-names-toxml = {
      expr = xmlCalls libSources > 0;
      expected = true;
    };

    # The domain, so a zero is not "the walk found no files".
    test-the-scan-reached-every-library-file = {
      expr = map (s: s.name) sources;
      expected = [
        "lib/apply.nix"
        "lib/catalogue.nix"
        "lib/default.nix"
        "lib/defunctionalize.nix"
        "lib/walk.nix"
        "flake.nix"
        "default.nix"
      ];
    };
  };
}
