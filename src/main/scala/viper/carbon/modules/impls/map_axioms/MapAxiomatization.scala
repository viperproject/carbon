// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

/**
; These axioms are based on the DafnyPrelude.bpl file of Microsoft's Dafny tool.
; See https://github.com/dafny-lang for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)
  */

package viper.carbon.modules.impls.map_axioms

object MapAxiomatization {
  val value : String =
    """
      |type Map U V;
      |
      |// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.
      |
      |function Map#Domain<U,V>(Map U V) : Set U;
      |
      |function Map#Elements<U,V>(Map U V) : [U]V;
      |
      |function Map#Card<U,V>(Map U V) : int;
      |
      |axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));
      |
      |// The set of Keys of a Map are available by Map#Domain, and the cardinality of that
      |// set is given by Map#Card.
      |
      |  /* added second trigger set */
      |
      |axiom (forall<U,V> m: Map U V :: { Set#Card(Map#Domain(m)) } { Map#Card(m) }
      |  Set#Card(Map#Domain(m)) == Map#Card(m));
      |
      |// The set of Values of a Map can be obtained by the function Map#Values, which is
      |// defined as follows.  Remember, a Set is defined by membership (using Boogie's
      |// square brackets) and Map#Card, so we need to define what these mean for the Set
      |// returned by Map#Values.
      |
      |function Map#Values<U,V>(Map U V) : Set V;
      |
      |  /* split axiom into each direction */
      |
      |axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
      |  Map#Values(m)[v] ==>
      |	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
      |	  Map#Domain(m)[u] &&
      |    v == Map#Elements(m)[u]));
      |
      |axiom (forall<U,V> m: Map U V, u: U ::  { Map#Elements(m)[u] } // { Map#Domain(m)[u] } // REMOVED this trigger due to a potential for matching loops
      |	  Map#Domain(m)[u]
      |    ==> Map#Values(m)[Map#Elements(m)[u]]);
      |// There's a potential for matching loops with the extra trigger if two maps have equal domains:
      |// v in range(m1); some k in dom(m1) = dom(m2) s.t. m1[k] = v; m2[k] in range(m2); some k' in dom(m2) s.t. m2[k'] = m2[k]
      |
      |axiom (forall<U,V> m: Map U V, u: U ::  { Map#Domain(m)[u] } { Map#Elements(m)[u] }
      |	  Map#Domain(m)[u]
      |    ==> Set#Card(Map#Values(m)) > 0); // weaker property than above, with weaker triggers
      |
      | // Here are the operations that produce Map values.
      |
      |function Map#Empty<U, V>(): Map U V;
      |axiom (forall<U, V> u: U ::
      |        { Map#Domain(Map#Empty(): Map U V)[u] }
      |        !Map#Domain(Map#Empty(): Map U V)[u]);
      |
      |axiom (forall<U, V> m: Map U V :: { Map#Card(m) }
      | (Map#Card(m) == 0 <==> m == Map#Empty()) &&
      | (Map#Card(m) != 0 ==> (exists x: U :: Map#Domain(m)[x])) &&
      | ((forall x: U :: {Map#Domain(m)[x]} Map#Domain(m)[x] ==> Map#Card(m) != 0)));
      |
      |//Build is used in displays, and for map updates
      |function Map#Build<U, V>(Map U V, U, V): Map U V;
      |
      |/* added second trigger set (cf. example3 test case, test3) */
      |axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
      |  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Domain(m)[u'],Map#Build(m, u, v) } { Map#Elements(Map#Build(m, u, v))[u'] }
      |  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
      |               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
      |  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
      |               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
      |/* added second trigger set (not sure of a test case needing it, though) */
      |axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }{ Map#Card(m),Map#Build(m, u, v) }
      |  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
      |/* added second trigger set (not sure of a test case needing it, though) */
      |axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }{ Map#Card(m),Map#Build(m, u, v) }
      |  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);
      |
      |//equality for maps
      |  // this axiom is only needed in one direction; the other is implied by the next axiom
      |
      |function Map#Equal<U, V>(Map U V, Map U V): bool;
      |axiom (forall<U, V> m: Map U V, m': Map U V::
      |  { Map#Equal(m, m') }
      |   (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
      |     (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]) ==> Map#Equal(m, m'));
      |// extensionality
      |axiom (forall<U, V> m: Map U V, m': Map U V::
      |  { Map#Equal(m, m') }
      |    Map#Equal(m, m') ==> m == m');
      |
      |function Map#Disjoint<U, V>(Map U V, Map U V): bool;
      |// split in both directions
      |axiom (forall<U, V> m: Map U V, m': Map U V ::
      |  { Map#Disjoint(m, m') }
      |    Map#Disjoint(m, m') ==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));
      |axiom (forall<U, V> m: Map U V, m': Map U V ::
      |  { Map#Disjoint(m, m') }
      |    !Map#Disjoint(m, m') ==> (exists o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} Map#Domain(m)[o] && Map#Domain(m')[o]));
      |
      |""".stripMargin
}
