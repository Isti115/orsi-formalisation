module Prototype_4.Util

%access public export
%default total

postulate typeDecidable : (A : Type) -> (Either (Not A) A)
