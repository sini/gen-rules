# A minimal framework over gen-rules, shared by the cells: options for an aspect tree, a rule set and
# the registration table; the loader is `defunctionalize` over each admitted module; the door is
# `mkApply` over the merged table; unit 2's guard vocabulary fires door nodes through it.
#
# Invented vocabulary throughout (ADR-0035): the coordinates are `thimble`, `bobbin` and `spool`.
{
  genRules,
  genAlgebra,
  genIdentity,
  genAspects,
  genProgram,
  genMerge,
  ...
}:
let
  R = genRules;
  merge = genMerge;
  aspects = genAspects;
  program = genProgram;
  T = genAlgebra.term genIdentity.hashIdentity;

  D = [
    "thimble"
    "bobbin"
    "spool"
  ];
  moduleArgs = {
    lib = true;
    config = true;
    options = true;
    pkgs = true;
    modulesPath = true;
    aspect = true;
  };
  cnfOf = d: {
    entityKinds = d;
    keySemantics.nixos.category = "class";
    inherit moduleArgs;
    aspectModules = [ (R.lambdasMount "lambdas") ];
  };

  # One framework evaluation: `modules` admitted through the loader, the door over the merged table.
  framework =
    {
      modules,
      d ? D,
      ruleContract ? {
        emits = [ "tuck" ];
        binds = null;
        suppresses = [ ];
      },
    }:
    let
      cnf0 = cnfOf d;
      load =
        i: m:
        R.defunctionalize {
          cnf = cnf0;
          declared = d;
          key = "fixture:${toString i}";
          lambdasPath = [
            "fw"
            "lambdas"
          ];
          aspectPaths = [
            [
              "fw"
              "aspects"
            ]
          ];
          rulePaths = [
            {
              path = [
                "fw"
                "rules"
              ];
              contract = ruleContract;
            }
          ];
        } m;
      decls = {
        options.fw.aspects = merge.mkOption {
          type = merge.lazyAttrsOf merge.raw;
          default = { };
        };
        options.fw.rules = merge.mkOption {
          type = merge.lazyAttrsOf merge.raw;
          default = { };
        };
        options.fw.lambdas = R.lambdas;
        config._module.args.pkgs = "PKGS";
      };
      r = merge.evalModuleTree { } (
        [
          decls
        ]
        ++ builtins.genList (i: load i (builtins.elemAt modules i)) (builtins.length modules)
      );
      door = R.mkApply {
        lambdas = r.config.fw.lambdas;
        cnf = cnf0;
        declared = d;
      };
      vocab = aspects.mkGuardVocab (cnf0 // { ref = door; });
    in
    {
      inherit r door;
      cnf = cnf0;
      config = r.config.fw;
      node = name: r.config.fw.aspects.${name};
      fire =
        context: sources: node:
        vocab.applyGuardWith {
          inherit context sources;
          scope = { };
        } node;
    };

  src = k: "entity:" + builtins.hashString "sha256" k;
  ctx = {
    thimble = "x";
    bobbin = "b";
    spool = "s";
    extra = "e";
  };
  srcs = {
    thimble = src "t";
    bobbin = src "b";
    spool = src "s";
    extra = src "e";
  };
in
{
  inherit
    R
    T
    D
    merge
    aspects
    program
    framework
    cnfOf
    moduleArgs
    src
    ctx
    srcs
    ;
  t = T.term;
  # A refusal value's code, `right` for a success: the cells read which arm the door took.
  code =
    r:
    if builtins.isAttrs r && r ? left then
      r.left.code
    else if builtins.isAttrs r && r ? right then
      "right"
    else
      r;
  # `tryEval` over a full force: a cell asserting THAT something refuses (the message is the error
  # plane's, `ci/tests-error.nix`).
  throws = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  # A door node's form: its condition's former, the coordinates it covers, its body's former, and the
  # reads decoded from its registration identifier.
  form = n: {
    formerOf = n.condition.__bodyTerm;
    covers = T.readCtxHeads n.condition;
    body = n.body.__bodyTerm;
    reads = (builtins.fromJSON n.body.id).declared.reads;
  };
  fire1 = f: name: f.fire ctx srcs (f.node name);
  tuck =
    {
      thimble,
      bobbin ? "d",
      ...
    }:
    {
      description = "tuck-${thimble}";
    };
}
