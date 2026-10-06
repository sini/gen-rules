# THE PUBLISHED SURFACE. Nothing else is exported: the pattern reader, the shared walk and the site
# encoder are internal. `finiteHeads` is deliberately absent: the over-approximation refusal belongs
# to the first analysis that reads a door rule's heads, and none exists.
{ genRules, ... }:
{
  flake.tests.surface = {
    test-the-published-surface = {
      expr = builtins.attrNames genRules;
      expected = [
        "abnormality"
        "conditionalEdge"
        "defunctionalize"
        "lambdas"
        "lambdasMount"
        "mkApply"
        "registrations"
      ];
    };
  };
}
