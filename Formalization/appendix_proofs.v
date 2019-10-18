
(*
    Since cases and cocases in our matches and comatches are always exhaustive and non-overlapping,
    changing their order in a match will not change the result of the one_step_eval function.
    Similarly, changing the ordering of any part of the surrounding program, like the list of cfun
    bodies, has no effect on evaluation.
    Hence, we only need to consider the three parts of the full xfunc algorithms in which
    substantial changes are performed:
    - lifting xmatches,
    - core xfunc,
    - inlining xmatches.
    Proofs for these three parts follow below.

    ------------------------------------------------------------------------------------------------

    Lemma R1.1: Given an expression expr, the result of (lift_match expr) will be a value iff expr
        is a value.
    Proof.
        We will perform an induction on the structure of expr.
        Most cases are congruence cases and thus trivial.
        The only interesing case is a match on the type in consideration.
        A match can never be a value and correspondingly, since
        match d on e using bs with
            ...
        with name d, expression e and bindings list bs will be translated into
        e'.d(bs'),
        where e' and bs' are the recursively translated expression e and bindings list bs,
        respectively, the result will also not be a value.
    Qed.

    Lemma D1.1: Given an expression expr, the result of (lift_comatch expr) will be a value iff expr
        is a value.
    Proof.
        We will perform an induction on the structure of expr.
        Most cases are congruence cases and thus trivial.
        The only interesing case is a comatch on the type in consideration.
        A comatch
        comatch C on T using bs with
            ...
        with name C, type T and bindings list bs is a value iff all expressions in bs are values and
        will be translated into
        C(bs')
        where bs' is the recursively translated bindings list bs.
        This result will also only be a value if bs' consists of values and thus we can conclude
        with the induction hypothesis.
    Qed.

    Lemma R1.2: Given an expression expr, the result of (lift_match expr) will be a redex iff expr
        is a redex.
    Proof.
        We will once again use induction over the structure of expr.
        Using progress, we can conclude that non-redexes are preserved, since they are values and
        thus will stay values according to Lemma R1.1.
        A redex is either a destructor call, a match or a cfun call.
        All other cases are immediate congruence cases and thus only require to check that the
        arguments stay values/non-values.
        This can be concluded by using Lemma R1.1.
        Similarly, the case of a destructor call is also a congruence case, since we are lifting
        matches and thus the type parameter of the lifting function is a data type and hence
        different from the type of the destructor in a destructor call.
        Likewise, the case of a cfun call is also not interesting, since cfun calls are not changed
        by the lifting (apart from congruence).
        In the case of a match, we have to differentiate between a match on the type under
        consideration and matches on a different type.
        In the latter case, we can once again apply our congruence rule and finish with the
        induction hypothesis.
        Finally, in the case of a match on the type onder consideration,
        match d on e using bs
            ...
        will once again be translated to
        e'.d(bs'),
        with e' and bs' being the recursively translated expression e and bindings list bs,
        respectively.
        The match will be a redex iff e and all expressions in bs are values.
        Similarly, the cfun call will be a redex iff and only e' and all expressions in bs' are
        values.
        This can easily be confirmed by application of Lemma R1.1, thus concluding the proof.
    Qed.

    Lemma D1.2: Given an expression expr, the result of (lift_comatch expr) will be a redex iff expr
        is a redex.
    Proof.
        We will once again use induction over the structure of expr.
        Using progress, we can conclude that non-redexes are preserved, since they are values and
        thus will stay values according to Lemma D1.1.
        A redex is either a destructor call, a match or a cfun call.
        All other cases are immediate congruence cases and thus only require to check that the
        arguments stay values/non-values.
        This can be concluded by using Lemma R1.1.
        Similarly, the case of a match or cfun call is also a congruence case, since we are lifting
        comatches and thus the type parameter of the lifting function is a codata type and hence
        different from the type of the type being matched on or the type of the cfun being called,
        respectively.
        In the case of a destructor call, we have to differentiate between a destructor call on the
        type under consideration and destructor call on a different type.
        In the latter case, we can once again apply our congruence rule and finish with the
        induction hypothesis.
        Finally, in the case of a destructor call on the type onder consideration,
        e.d(bs)
        will once again be translated to
        e'.d(bs'),
        with e' and bs' being the recursively translated expression e and bindings list bs,
        respectively.
        If e is a gfun call, the result will be the same gfun call with recursively translated
        arguments and it is hence another congruence case.
        If e is a comatch
        comatch C on T using cs with
            ...
        then it will be translated into
        C(cs'),
        with cs' being the recursively translated arguments (with removed type annotations).
        Thus, the result C(cs').d(bs')
        will be a redex iff all expressions in cs' and bs' are values.
        Using Lemma D1.1, this is the case iff cs and bs consist of values, which is precisely iff
        the original expression is a redex.
    Qed.


    Lemma D1.3 Given an expression expr,
        one_step_eval (lift_match expr) = lift_match (one_step_eval expr),
        i.e. lift_match preserves reduction.
    Proof.
        First, fix T to be the type of matches to be lifted.
        We will perform an induction on the structure of expr.
        Since, by Lemmas D1.1 and D1.2, lifting preserves values and redexes, we only need to
        consider the case of redexes which involve a match on a constructor of T where all arguments
        and expressions in the bindings list are already values, since all other cases are once
        again congruences that can immediately be handled by induction.
        In the remaining case, we have
        match d on C(as) using ws:bs returning T' with
            ...
            C(vs) => e
            ...
        with d and C being names for the match and a constructor for T, respectively, as a list of
        values, ws:bs a bindings list (i.e. ws a list of variables and bs the corresponding list of
        values), vs a list of variables and e an expression.
        Reducing this by one step would result in
        e[vs -> as][ws -> bs],
        i.e. substituting the variables vs by the values as and substituting the variables specified
in bs by their corresponding values.
        The result of lifting this expression would be
        C(as').d'(bs'),
        where as and bs are the result of recursively performing lifting in as and bs (and in the
        latter case, removing type annotations), respectively, and d' is the name of the cfun
        corresponding to the match d.
        Additionally, there would be a new cfun in the program, with body
        cfun T : d'(ws) : T' :=
            ...
            C(vs) => e'
            ...
        with e' being the result of performing lifting in e.
        Reducing C(as').d'(bs') would result in
        e'[vs -> as'][ws -> bs'].
        By the substition lemma lift_match_subst, this is also the result of lifting 
        e[vs -> as][ws -> bs].
    Qed.

    Lemma R1.3 Given an expression expr,
        one_step_eval (lift_comatch expr) = lift_comatch (one_step_eval expr),
        i.e. lift_comatch preserves reduction.
    Proof.
        First, fix T to be the type of matches to be lifted.
        We will perform an induction on the structure of expr.
        Since, by Lemmas R1.1 and R1.2, lifting preserves values and redexes, we only need to
        consider the case of redexes which involve a destructor call on a comatch on T where all
        arguments and expressions in the bindings list are already values, since all other cases are
        once again congruences that can immediately be handled by induction.
        In the remaining case, we have
        comatch C on T using ws:bs with
            ...
            d(vs) => e
            ...).d(as).
        with C and d being names for the comatch and a destructor for T, respectively, as a list of
        values, ws:bs a bindings list (i.e. ws a list of variables and bs the corresponding list of
        values), vs a list of variables and e an expression.
        Reducing this by one step would result in
        e[vs -> as][ws -> bs],
        i.e. substituting the variables vs by the values as and substituting the variables specified
        in bs by their corresponding values.
        The result of lifting this expression would be
        C'(as').d(bs'),
        where as and bs are the result of recursively performing lifting in as and bs (and in the
        latter case, removing type annotations), respectively, and C' is the name of the gfun
        corresponding to the comatch C.
        Additionally, there would be a new dfun in the program, with body
        dfun C'(ws) : T :=
            ...
            d(vs) => e'
            ...
        with e' being the result of performing lifting in e.
        Reducing C'(as').d(bs') would result in
        e'[vs -> as'][ws -> bs'].
        By the substition lemma lift_comatch_subst, this is also the result of lifting
        e[vs -> as][ws -> bs].
    Qed.

    ------------------------------------------------------------------------------------------------

    Lemma R2.1: Given an expression expr, the result of (destructorize expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be destructorized.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some constructor C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        If it is of the first form C(as), then it is a value iff all expressions in as are values.
        The result of destructorization of C(as) will be
        C'(as'),
        where C' is the new gfun corresponding to C and as' are the recursively destructorized
        arguments.
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
        Similarly, in the second case, e.d(as) is not a value and its destructorization is
        e'.d'(as')
        with e' the destructorization of e, d' the new destructor corresponding to d and as' the
        recursively destructorized list as.
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma D2.1: Given an expression expr, the result of (constructorize expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be destructorized.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a destructor d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        If it is of the first form C(as), then it is a value iff all expressions in as are values.
        The result of constructorization of C(as) will be
        C'(as'),
        where C' is the new constructor corresponding to C and as' are the recursively
        constructorized arguments.
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
        Similarly, in the second case, e.d(as) is not a value and its constructorization is
        e'.d'(as')
        with e' the constructorization of e, d' the new cfun corresponding to d and as' the
        recursively constructorized list as.
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma R2.2: Given an expression expr, the result of (destructorize expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be destructorized.
        We start by induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some constructor C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma R2.1.
        If it is of the first form C(as), then it is not an outermost redex.
        The result of destructorization of C(as) will be
        C'(as'),
        where C' is the new gfun corresponding to C and as' are the recursively destructorized
        arguments.
        This also can never be a redex.
        Similarly, in the second case, e.d(as) is a redex iff e and all expressions in as are values
        and its destructorization is
        e'.d'(as')
        with e' the destructorization of e, d' the new destructor corresponding to d and as' the
        recursively destructorized list as.
        This is a redex iff e' and all expressions in as' are values, which by Lemma R2.1 is the
        case iff e and all expressions in as are values, which is once again is true iff the
        e.d(as) is a redex.
    Qed.

    Lemma D2.2: Given an expression expr, the result of (constructorize expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be constructorized.
        We start by induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a destructor d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma D2.1.
        If it is of the first form C(as), then it is not an outermost redex.
        The result of constructorization of C(as) will be
        C'(as'),
        where C' is the new constructor corresponding to C and as' are the recursively
        constructorized arguments.
        This also can never be a redex.
        Similarly, in the second case, e.d(as) is a redex iff e and all expressions in as are values
        and its constructorization is
        e'.d'(as')
        with e' the constructorization of e, d' the new cfun corresponding to d and as' the
        recursively constructorized list as.
        This is a redex iff e' and all expressions in as' are values, which by Lemma D2.1 is the
        case iff e and all expressions in as are values, which is once again is true iff the
        e.d(as) is a redex.
    Qed.

    Lemma R2.3 Given an expression expr,
        one_step_eval (destructorize expr) = destructorize (one_step_eval expr),
        i.e. destructorize preserves reduction.
    Proof.
        First, fix T to be the type to be destructorized.
        We will perform an induction on the structure of expr.
        Since, by Lemmas R2.1 and R2.2, destructorization preserves values and redexes, we only
        need to consider the case of redexes which involve a cfun call on a constructor on T where
        all arguments are already values, since all other cases are once again congruences that can
        immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a constructor and a cfun on T,
        respectively.
        Furthermore, we have a cfun
        cfun T: d(ws) : T' :=
            ...
            C(vs) => e
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After destructorization, we get
        C'(as').d'(bs'),
        with as' and bs' being the recursively destructorized expression list as and bs,
        respectively, and C' and d' being the new corresponding gfun and destructor names,
        respectively.
        Additionally, we replace the cfun d by a new gfun
        gfun C(vs) : T :=
            ...
            d(ws) => e'
            ...
        with variable lists vs and ws as well as the expression e', which is the result of
        destructorizing e.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma dtorize_substitution, is the result of destructorizing
        e[vs -> as][ws -> bs].
    Qed.

    Lemma D2.3 Given an expression expr,
        one_step_eval (constructorize expr) = constructorize (one_step_eval expr),
        i.e. constructorize preserves reduction.
    Proof.
        First, fix T to be the type to be constructorized.
        We will perform an induction on the structure of expr.
        Since, by Lemmas D2.1 and D2.2, constructorization preserves values and redexes, we only
        need to consider the case of redexes which involve a destructor call on a gfun on T where
        all arguments are already values, since all other cases are once again congruences that can
        immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a gfun and a destructor on T,
        respectively.
        Furthermore, we have a gfun
        gfun T: d(ws) : T' :=
            ...
            C(vs) => e
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After constructorization, we get
        C'(as').d'(bs'),
        with as' and bs' being the recursively constructorized expression list as and bs,
        respectively, and C' and d' being the new corresponding constructor and cfun names,
        respectively.
        Additionally, we replace the gfun d by a new cfun
        cfun d(ws) : T :=
            ...
            C(vs) => e'
            ...
        with variable lists vs and ws as well as the expression e', which is the result of
        constructorizing e.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma ctorize_substitution, is the result of constructorizing
        e[vs -> as][ws -> bs].
    Qed.

    ------------------------------------------------------------------------------------------------

    Lemma R3.0: Given a variable v, expressions expr and expr1 inside a program p where every local
        gfun is called at most once, we have
        inline_comatch expr[v -> expr1] = (inline_comatch expr)[v -> inline_comatch expr1],
        inline_comatch preserves substitution.
        Note: Since local gfuns are called at most once inside p, this means that it cannot both
        occur in expr and expr1.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        Since inline_comatch is repeatedly inlining one comatch at a time, it suffices to consider
        one of these steps.
        We will perform an induction on the structure of expr.
        All cases except a local gfun call are once again congruence cases, which can be dealt with
        by induction.
        In the remaining case, we have a gfun call
        C(as)
        for some gfun C of T with body
        gfun C(vs) : T :=
            d_i(ws_i) => e_i
        Since there may at most one local gfun call for C, thus neither the body of C (i.e. all the
        expressions e_i) nor any of the expressions in as may contain a call to C.
        Now consider another expression e, which is also part of the program and thus may not
        contain a call to C.
        - Then substituting e for a variable v in the expression will result in
            C(as)[v -> e] = C(as[v -> e]).
            Performing inlining on this will result in 
            comatch C on T with vs:as'[v -> e'] with
                d_i(ws_i) => e_i',
            where as', e' and the e_i' are the results of inlining in the expression of as, in e
            and in the e_i, respectively (the e_i are also subject to inlining because inlining
            affects the whole program).
            However, since we know that there can be no gfun call to C in as, e or the e_i, this is
            the same as
            comatch C on T with vs:as[v -> e] with
                d_i(ws_i) => e_i.
        - After inlining in the original expression, we get
            comatch C on T with vs:as' with
                d_i(ws_i) => e_i',
            where as' and the e_i' are the results of inlining in the expression of as and in the
            e_i, respectively.
            However, since we know that there can be no gfun call to C in as, e or the e_i, this is
            the same as
            comatch C on T with vs:as with
                d_i(ws_i) => e_i.
            Performing inlining on e will be the identity, since by our prerequisites e may not
            contain a call to C.
            Performing substitution of e in the result of inlining the original expression, we get
            comatch C on T with vs:as[v -> e] with
                d_i(ws_i) => e_i.
            which is the same result as performing substitution and inlining in the reverse order.
    Qed.

    Lemma D3.0: Given a variable v, expressions expr and expr1 inside a program p where every local
        cfun is called at most once, we have
        inline_match expr[v -> expr1] = (inline_match expr)[v -> inline_match expr1],
        inline_match preserves substitution.
        Note: Since local cfuns are called at most once inside p, this means that it cannot both
        occur in expr and expr1.
    Proof.
        First, fix T to be the type of the cfuns to be inlined.
        Since inline_match is repeatedly inlining one match at a time, it suffices to consider one
        of these steps.
        We will perform an induction on the structure of expressions.
        All cases except a local cfun call are once again congruence cases, which can be dealt with
        by induction.
        In the remaining case, we have a gfun call
        ex.d(as)
        for some expression ex and some cfun d of T with body
        cfun T: d(vs) : T' :=
            C_i(ws_i) => e_i
        Since tfere may at most one local cfun call for d, thus neither the body of d (i.e. all the
        expressions e_i) nor ex or any of the expressions in as may contain a call to d.
        Now consider another expression e, which is also part of the program and thus may not
        contain a call to d.
        - Then substituting e for a variable v in the expression will result in
            ex.d(as)[v -> e] = ex[v -> e].d(as[v -> e]).
            Performing inlining on this will result in 
            match d on ex'[v -> e'] with vs:as'[v -> e'] with
                C_i(ws_i) => e_i',
            where as', e', ex' and the e_i' are the results of inlining in the expression of as, in
            e, in ex and in the e_i, respectively (the e_i are also subject to inlining because
            inlining affects the whole program).
            However, since we know that there can be no cfun call to d in as, e, ex or the e_i, this
            is the same as
            match d on ex[v -> e] with vs:as[v -> e] with
                C_i(ws_i) => e_i.
        - After inlining in the original expression, we get
            match d on ex' with vs:as' with
                C_i(ws_i) => e_i',
            where as', ex' and the e_i' are the results of inlining in the expression of as, in ex
            and in the e_i, respectively.
            However, since we know that there can be no cfun call to d in as, e, ex or the e_i, this
            is the same as
            match d on ex with vs:as with
                C_i(ws_i) => e_i.
            Performing inlining on e will be the identity, since by our prerequisites e may not
            contain a call to d.
            Performing substitution of e in the result of inlining the original expression, we get
            match d on ex[v -> e] with vs:as[v -> e] with
                C_i(ws_i) => e_i.
            which is the same result as performing substitution and inlining in the reverse order.
    Qed.

    Lemma R3.1: Given an expression expr, the result of (inline_comatch expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        In the remaining case, C(as) it is a value iff all expressions in as are values.
        The result of inlining C(as) will be
        comatch C on T using as' with
            ...,
        where as' is the result of recursively inlining in as (with added type annotations from the
        signature of the gfun C).
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
    Qed.

    Lemma D3.1: Given an expression expr, the result of (inline_match expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        In the remaining case, e.d(as) is not a value and the result of inlining is
        match d on e' using as' with
            ...,
        with e' the result of inlining in e and as' the result of recursively inlining in as (with
        added type annotations from the signature of the cfun d).
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma R3.2: Given an expression expr, the result of (inline_comatch expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        or
        C(as).d(bs)
        for some local gfun C of type T, lists of expressions as and bs, and a destructor d on T,
        then this is a simple congruence case, which can immediately be resolved by induction.
          - In the first remaining case, C(as) is not a redex.
            The result of inlining C(as) will be
            comatch C on T using as' with
                ...,
            where as' is the result of recursively inlining in as (with added type annotations from
            the signature of the gfun C).
            This is also not a redex.
          - In the second remaining case, C(as).d(bs) is a redex.
            The result of inlining will be
            (comatch C on T using as' with
                ...).d(bs'),
            where as' and bs' are the result of recursively inlining in as (with added type
            annotations from the signature of the gfun C) and bs.
            This is also a redex.
    Qed.

    Lemma D3.2: Given an expression expr, the result of (inline_match expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be inlined.
        We will perform an induction on the structure of expressions.
        If the input expression is not of the form
        e.d(as)
        for some expression e of type T, a local cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma R3.1.
        In the remaining case, e.d(as) is a redex iff e and all expressions in as are values and the
        result of inlining is
        match d on e' using as' with
            ...,
        with e' the result of inlining in e and as' the result of recursively inlining in as (with
        added type annotations from the signature of the cfun d).
        This is a redex iff e' and all expressions in as' are values, which, by using Lemma R3.1 is
        true iff e and all expressions in as are values, which holds iff e.d(as) is a redex.
    Qed.

    Lemma R3.3 Given an expression expr,
        one_step_eval (inline_comatch expr) = inline_comatch (one_step_eval expr),
        i.e. inline_comatch preserves reduction.
    Proof.
        First, fix T to be the type of comatches to be inlined.
        We will perform an induction on the structure of expressions.
        Since, by Lemmas R3.1 and R3.2, inlining preserves values and redexes, we only
        need to consider the case of redexes which involve a destructor call on a local gfun on T
        where all arguments are already values, since all other cases are once again congruences
        that can immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a local gfun and a destructor on
        T, respectively.
        Furthermore, we have a gfun
        gfun C(vs) : T :=
            ...
            d(ws) => e'
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After inlining, we get
        (comatch C on T using vs:as' with
            ...
            d(ws) => e'
            ...).d(bs')
        with as' and bs' being the results of recursively inlining expression on lists as and bs,
        respectively, ws and vs being variable lists, and e' being the result of recursively
        inlining on e.
        Additionally, we remove the gfun C.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma R3.0, is the result of performing inlining on
        e[vs -> as][ws -> bs].
    Qed.

    Lemma D3.3 Given an expression expr,
        one_step_eval (inline_match expr) = inline_match (one_step_eval expr),
        i.e. inline_match preserves reduction.
    Proof.
        First, fix T to be the type of matches to be inlined.
        We will perform an induction on the structure of expressions.
        Since, by Lemmas D3.1 and D3.2, inlining preserves values and redexes, we only
        need to consider the case of redexes which involve a local cfun call on a constructor on T
        where all arguments are already values, since all other cases are once again congruences
        that can immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a constructor and a local cfun on
        T, respectively.
        Furthermore, we have a cfun
        cfun T: d(ws) : T' :=
            ...
            C(vs) => e'
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After inlining, we get
        match d on C(as') using vs:bs' with
            ...
            C(vs) => e'
            ...
        with as' and bs' being the results of recursively inlining expression on lists as and bs,
        respectively, ws and vs being variable lists, and e' being the result of recursively
        inlining on e.
        Additionally, we remove the cfun d.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma D3.0, is the result of performing inlining on
        e[vs -> as][ws -> bs].
    Qed.

*)
