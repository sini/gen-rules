# The pattern catalogue (design Section 4; Q10 (b)). THE PATTERN CONTRACT: a pattern takes terms, emits
# gen-program declarations in the terms-only algebra, and evaluates nothing. Each lowers to positive
# and negative literals through gen-program's literal tier (`declaration.when`), so an absent atom is
# FALSE under ADR-0020's well-founded model.
#
# The pair is McCarthy's, as Przymusinski 1988 Example 9 states it: "unless something is abnormal, the
# result of moving X onto Y is that X is on Y" (`on ← ¬ab`), and "the situation is abnormal if …"
# (`ab ← …`). A conditional edge is the first clause; an abnormality is the second.
{ T }:
let
  inherit (builtins) isString;
  tm = T.term;
  need =
    who: field: ok: v:
    if ok v then
      v
    else
      throw "gen-rules.${who}: `${field}` ${
        if field == "when" then
          "is a condition term (has, not, all, always)"
        else
          "is an atom: a string the caller writes"
      }; received a ${builtins.typeOf v}";

  # Every field is checked by name, so an honest omission (a forgotten `unless`) is a catchable refusal
  # and never a missing-argument abort; `unless = null` is written, because absence is a decision.
  fields =
    who: required: optional: args:
    let
      missing = builtins.filter (f: !(args ? ${f})) required;
      extra = builtins.filter (f: !(builtins.elem f (required ++ optional))) (builtins.attrNames args);
    in
    if !(builtins.isAttrs args) then
      throw "gen-rules.${who}: takes a record { ${builtins.concatStringsSep "; " required}; }"
    else if missing != [ ] then
      throw "gen-rules.${who}: missing ${builtins.toJSON missing}${
        if builtins.elem "unless" missing then
          " (`unless = null` is written for an edge no abnormality defeats)"
        else
          ""
      }"
    else if extra != [ ] then
      throw "gen-rules.${who}: unknown field(s) ${builtins.toJSON extra}"
    else
      args;

  # conditionalEdge { head; when; unless; relata; label ? null; }      head ← when, ¬unless
  conditionalEdge =
    args:
    let
      a = fields "conditionalEdge" [ "head" "when" "unless" "relata" ] [ "label" ] args;
      w = need "conditionalEdge" "when" T.isTerm a.when;
      u = if a.unless == null then null else need "conditionalEdge" "unless" isString a.unless;
    in
    [
      {
        head = need "conditionalEdge" "head" isString a.head;
        inherit (a) relata;
        label = a.label or null;
        when =
          if u == null then
            w
          else
            tm.all [
              w
              (tm.not (tm.has u))
            ];
      }
    ];

  # abnormality { head; when; relata; }      head ← when
  abnormality =
    args:
    let
      a = fields "abnormality" [ "head" "when" "relata" ] [ ] args;
    in
    [
      {
        head = need "abnormality" "head" isString a.head;
        when = need "abnormality" "when" T.isTerm a.when;
        inherit (a) relata;
      }
    ];
in
{
  inherit conditionalEdge abnormality;
}
