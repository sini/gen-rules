# The S1 arm (a) framework (den-hoag-lwbb1): gen-rules' `lambdas` mounted inside gen-aspects' aspect
# submodule by `lambdasMount` in `cnf.aspectModules`, the one cnf handed to the schema, the loader and the
# door. Shared by `../s1.nix` and `../../tests-error.nix`.
{
  genRules,
  genAlgebra,
  genIdentity,
  genAspects,
  genProgram,
  genMerge,
  ...
}@args:
let
  w = import ./world.nix args;
  inherit (w) R merge aspects;
  keySemantics.nixos.category = "class";
  D = [
    "thimble"
    "bobbin"
  ];
  src = k: "entity:" + builtins.hashString "sha256" k;
  ctx = {
    thimble = "x";
    bobbin = "b";
  };
  srcs = {
    thimble = src "t";
    bobbin = src "b";
  };
  inner = { thimble, ... }: { description = "T-${thimble}"; };
  at = [ "lambdas" ];
  framework =
    {
      modules,
      closed ? false,
    }:
    let
      cnf0 = {
        entityKinds = if closed then D else null;
        inherit keySemantics;
        inherit (w) moduleArgs;
        aspectModules = [ (R.lambdasMount "lambdas") ];
      };
      declared = if closed then D else null;
      schema = aspects.mkAspectSchema cnf0;
      load =
        i:
        R.defunctionalize {
          cnf = cnf0;
          inherit declared;
          key = "s1:${toString i}";
          lambdasPath = at;
          aspectPaths = [ [ "aspects" ] ];
        };
      r = merge.evalModuleTree { } (
        [
          { options.schema = schema.schemaOption; }
          (schema.mkAspectModule { })
          {
            options.lambdas = R.lambdas;
            config._module.args.pkgs = "PKGS";
          }
        ]
        ++ builtins.genList (i: load i (builtins.elemAt modules i)) (builtins.length modules)
      );
      door = R.mkApply {
        lambdas = r.config.lambdas;
        cnf = cnf0;
        inherit declared;
      };
      vocab = aspects.mkGuardVocab (cnf0 // { ref = door; });
    in
    {
      inherit r door;
      fire =
        context: node:
        vocab.applyGuardWith {
          inherit context;
          sources = srcs;
          scope = { };
        } node;
    };
  # Every registration identifier, once: gen-rules' own enumerator (an instrument's read).
  registered = R.registrations;
  isGuard = x: builtins.isAttrs x && (x.__guard or false);
  # door nodes in an aspect's includes, descending into include elements that are aspects
  guardsIn =
    a:
    builtins.concatMap (
      x:
      if isGuard x then
        [ x ]
      else if builtins.isAttrs x && x ? includes then
        guardsIn x
      else
        [ ]
    ) (a.includes or [ ]);
  classMarker =
    m:
    (merge.evalModuleTree { } [
      {
        options.marker = merge.mkOption {
          type = merge.types.str;
          default = "none";
        };
      }
      { config._module.args.pkgs = "P"; }
      m
    ]).config.marker;
  out =
    o:
    if o == null then
      "not-fired"
    else if o ? nixos then
      { nixos = classMarker o.nixos; }
    else
      o;
  run =
    {
      modules,
      closed ? false,
      context ? ctx,
      name ? "main",
    }:
    let
      f = framework { inherit modules closed; };
      nodes = guardsIn f.r.config.aspects.${name};
    in
    {
      registrations = builtins.length (registered f.r.config.lambdas);
      conditions = map (n: n.condition) nodes;
      fired = map (n: out (f.fire context n)) nodes;
    };
  ids =
    modules: name:
    let
      f = framework { inherit modules; };
    in
    {
      ids = registered f.r.config.lambdas;
      refs = map (n: n.body.id) (guardsIn f.r.config.aspects.${name});
    };
  # A module, keyed explicitly, writing `inner` inside a module function at `main` (or, as its
  # control, outside one).
  A = inResult: {
    key = "mod-A";
    config.aspects.main =
      if inResult then { config, ... }: { includes = [ inner ]; } else { includes = [ inner ]; };
  };
  B = cond: {
    key = "mod-B";
    config.aspects.main.includes = merge.mkIf cond [ { description = "plain"; } ];
  };
  C = {
    key = "mod-C";
    config.aspects.side.description = "unrelated";
  };
  Am = cond: {
    key = "mod-Am";
    config.aspects.main = merge.mkMerge [
      (merge.mkIf cond { includes = [ ({ bobbin, ... }: { description = "O-${bobbin}"; }) ]; })
      ({ config, ... }: { includes = [ inner ]; })
    ];
  };
  shared = { config, ... }: { includes = [ inner ]; };
  pinnedVsControl = p: c: {
    pinned = run p;
    control = run c;
  };
in
{
  inherit
    w
    D
    src
    ctx
    srcs
    inner
    at
    framework
    isGuard
    registered
    guardsIn
    classMarker
    out
    run
    ids
    A
    B
    C
    Am
    shared
    pinnedVsControl
    ;
  inherit (w) T;
}
