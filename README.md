# Formalization of the [HoTT Book](https://github.com/HoTT/book) in Agda.

A formalization of the Homotopy Type Theory Book in Agda.

The code can be explored in our [github page](https://shiranaiyo.github.io/HoTT-Book-Agda/index.html).

I've tried to keep the Agda as simple as possible, while using similar naming conventions to the HoTT book.
Some workarounds have to be done sometimes to please agda, I've tried to mention them somehow when the need arises.

Like the book, function extensionality and univalence are assumed, as well as the existence of HITs.
Unlike it, I take careful track of the universe indices (mainly to please agda).

### Acknowledgments

A lot of my code is taken from Escardo's [notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html).
Other references I used where [agda-unimath](https://unimath.github.io/agda-unimath/), Rijke's [formalization](https://github.com/HoTT-Intro/Agda) of his book, the [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) library, and of course Agda's [standard library](https://github.com/agda/agda-stdlib).

The css styles were taken from the [HoTTEST summer school](https://github.com/martinescardo/HoTTEST-Summer-School) repo.

### Contributing

Any contribution, be it in improving the readability of a proof, additional content from the book (I've skipped a ton), or just a simple typo is appreciated.
