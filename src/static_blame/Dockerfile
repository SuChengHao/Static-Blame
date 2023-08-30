FROM ubuntu:jammy
RUN apt-get update -y \
    && apt-get install -y haskell-stack racket ca-certificates curl sqlite3 libssl-dev \
    && raco pkg install --auto megaparsack \
    && raco pkg install --auto syntax/parse
CMD ["/bin/bash"]
