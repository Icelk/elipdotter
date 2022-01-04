-   [x] Occurences of AND statements, which occurence is shown? Have a list?
        Do this using UnsafeCell to get ref to vec. If eq two in Query::occurence, write to it.
        Have static "conditional_points" which store these.
-   [x] rate result, including proximity (do while running or ↑?) (reversed for NOT), how close ↓ was, etc.
-   [x] string proximity - give back iterator with all similar words.
        Have struct with iter of words, and the docs within that word.
        Then, read word till end, then advance words, etc.
    -   [ ] Make this affect the rating.
-   [x] Have AND NOT return results when they are in the same doc, but with lower rating.
        This is achieved through not making the difference, but filter_map the value. Then, modify it's rating to if they are both in, and remove those in `b`.
        Do this through <https://docs.rs/iter-set/2.0.2/iter_set/fn.classify.html>
