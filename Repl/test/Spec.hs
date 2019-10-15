import Test.Hspec (hspec, describe, it, shouldSatisfy, Expectation, shouldBe)
import Test.QuickCheck
import Data.Either (isRight, isLeft)

import AST
import UBProgram
import Plumbing
import Parser
import Coexample (natprogSkeleton)

shouldNotParse :: Show b =>  Parser b -> String -> Expectation
shouldNotParse parserP input = (parser (skeletonToState natprogSkeleton) parserP input) `shouldSatisfy` isLeft

shouldParseInputAs :: (Show b, Eq b) => Parser b -> String -> b -> Expectation
shouldParseInputAs parserP input result =
  (parser (skeletonToState natprogSkeleton) parserP input) `shouldSatisfy` test
    where
      test (Left _) = False
      test (Right e) = e == result

main :: IO ()
main = hspec $ do
  describe "Parser" $ do
    describe "nameP" $ do
      it "throws an error for the empty string" $ do
        nameP `shouldNotParse` ""
      it "throws an error for the string \"_\" " $ do
        nameP `shouldNotParse` "_"
      it "throws an error on keyword \"match\" " $ do
        nameP `shouldNotParse` "match"
      it "throws an error on keyword \"_match\" " $ do
        nameP `shouldNotParse` "_match"
      it "throws an error on name \"_foo\"" $ do
        nameP `shouldNotParse` "_foo"
      it "parses \"foo\" as name \"foo\"" $ do
        nameP `shouldParseInputAs` "foo" $ "foo"

    describe "localNameP" $ do
      it "throws an error for the empty string" $ do
        localNameP `shouldNotParse` ""
      it "throws an error for the string \"_\" " $ do
        localNameP `shouldNotParse` "_"
      it "throws an error on keyword \"match\" " $ do
        localNameP `shouldNotParse` "match"
      it "throws an error on keyword \"_match\" " $ do
        localNameP `shouldNotParse` "_match"
      it "throws an error on name \"foo\"" $ do
        localNameP `shouldNotParse` "foo"
      it "parses \"_foo\" as name \"foo\"" $ do
        localNameP `shouldParseInputAs` "_foo" $ "foo"

    describe "qNameP" $ do
      it "throws an error for the empty string" $ do
        qNameP `shouldNotParse` ""
      it "throws an error for the string \"_\" " $ do
        qNameP `shouldNotParse` "_"
      it "throws an error on keyword \"match\" " $ do
        qNameP `shouldNotParse` "match"
      it "throws an error on keyword \"_match\" " $ do
        qNameP `shouldNotParse` "_match"
      it "throws an error on name \"_foo\"" $ do
        qNameP `shouldNotParse` "_foo"
      it "throws an erro on name \"foo\"" $ do
        qNameP `shouldNotParse` "foo"
      it "parses \"zero\" as \"Nat:zero\"" $ do
        qNameP `shouldParseInputAs` "zero" $ ("Nat", "zero")
      it "parses \"true\" as \"Bool:true\"" $ do
        qNameP `shouldParseInputAs` "true" $ ("Bool", "true")

    describe "scopedNameP" $ do
      it "throws an error for the empty string" $ do
        scopedNameP `shouldNotParse` ""
      it "throws an error for the string \"_\" " $ do
        scopedNameP `shouldNotParse` "_"
      it "throws an error on keyword \"match\" " $ do
        scopedNameP `shouldNotParse` "match"
      it "throws an error on keyword \"_match\" " $ do
        scopedNameP `shouldNotParse` "_match"
      it "throws an error on name \"_foo\"" $ do
        scopedNameP `shouldNotParse` "_foo"
      it "throws an erro on name \"foo\"" $ do
        scopedNameP `shouldNotParse` "foo"
      it "parses \"zero\" as \"Global Nat:zero\"" $ do
        scopedNameP `shouldParseInputAs` "zero" $ (Coq_global ("Nat", "zero"))
      it "parses \"_succ\" as \"Local Nat:succ\"" $ do
        scopedNameP `shouldParseInputAs` "_succ" $ (Coq_local ("Nat", "succ"))

    describe "dataTypeP" $ do      
      it "throws an error for the empty string" $ do
        dataTypeP `shouldNotParse` ""
      it "correctly parses no constructors if next line is not indented" $ do
        dataTypeP `shouldParseInputAs` "data Nat where\nSOMETEXT" $
          ("Nat", [])
      it "throws an error if constructors are differently indented (1)" $ do
        dataTypeP `shouldNotParse` "data Nat where\n zero()\n  succ(Nat)" 
      it "throws an error if constructors are differently indented (2)" $ do
        dataTypeP `shouldNotParse` "data Nat where\n  zero()\n succ(Nat)"
      it "correctly parses the Nat datatype" $ do
        dataTypeP `shouldParseInputAs` "data Nat where\n  zero[]\n  succ[Nat]" $
          ("Nat", [(Coq_global ("Nat", "zero"),[]), (Coq_global ("Nat", "succ"), ["Nat"])])
      it "correctly parses a constructor with 2 arguments" $ do
        dataTypeP `shouldParseInputAs` "data XType where\n  cname[Typeone, Typetwo]" $
          ("XType", [(Coq_global ("XType", "cname"),["Typeone", "Typetwo"])])

    describe "coDataTypeP" $ do
      it "throws an error for the empty string" $ do
        coDataTypeP `shouldNotParse` ""
      it "correctly parses the Fun codata type" $ do
        coDataTypeP `shouldParseInputAs` "codata Fun where\n  apply(Nat) : Nat" $
          ("Fun", [((Coq_global ("Fun", "apply"), ["Nat"]), "Nat")])
      it "correctly parses no destructors if next line is not indented" $ do
        coDataTypeP `shouldParseInputAs` "codata Fun where\nSOMETEXT" $
          ("Fun", [])
      it "throws an error if destructors are differently indented (1)" $ do
        coDataTypeP `shouldNotParse` "codata Fun where\n apply1() : Nat\n  apply2() : Nat"
      it "throws an error if destructors are differently indented (2)" $ do
        coDataTypeP `shouldNotParse` "codata Fun where\n  apply1() : Nat\n apply2() : Nat"
      it "correctly parses a destructor with 2 arguments" $ do
        coDataTypeP `shouldParseInputAs` "codata Fun where\n apply(Nat, Nat) : Nat" $
          ("Fun", [(((Coq_global ("Fun", "apply")), ["Nat", "Nat"]), "Nat")])
