-   [x] Occurences of AND statements, which occurrence is shown? Have a list?
        Do this using UnsafeCell to get ref to vec. If eq two in Query::occurence, write to it.
        Have static "conditional_points" which store these.
-   [x] rate result, including proximity (do while running or ↑?) (reversed for NOT), how close ↓ was, etc.
-   [x] string proximity - give back iterator with all similar words.
        Have struct with iter of words, and the docs within that word.
        Then, read word till end, then advance words, etc.
    -   [ ] Make this affect the rating.
    -   [ ] Maybe use https://docs.rs/strsim/0.10.0/strsim/fn.hamming.html, but make the longer string the same len as the shorter. Then, add the diff of the len of them.
            Use 1/(0.1x + 1) to get a jaro-like value.
-   [x] Have AND NOT return results when they are in the same doc, but with lower rating.
        This is achieved through not making the difference, but filter_map the value. Then, modify it's rating to if they are both in, and remove those in `b`.
        Do this through <https://docs.rs/iter-set/2.0.2/iter_set/fn.classify.html>
-   [ ] Remove from index when missing occurrences were found.
-   [ ] Where to input `word_count_limit`?
-   [x] Make hit start the closest with others - the one which heightens the rating.
