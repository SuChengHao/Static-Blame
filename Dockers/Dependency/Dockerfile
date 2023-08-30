#syntax=docker/dockerfile:1
FROM ubuntu:kinetic
RUN sed -i 's/archive.ubuntu.com/mirror.nju.edu.cn/g' /etc/apt/sources.list && apt-get update -y \
    && apt-get install -y --no-install-recommends zlib1g-dev haskell-stack racket ca-certificates curl sqlite3 libssl-dev libeditreadline-dev llvm-11-dev libllvm11 clang-11 clang-tools-11 libclang-11-dev git
ENV SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt
ENV SSL_CERT_DIR=/etc/ssl/certs
ENV LLVM_CONFIG=llvm-config-11
RUN raco pkg install --auto megaparsack && raco pkg install --auto fmt && raco pkg install --auto mutate && raco pkg install --auto pprint \
    && raco pkg install --auto https://github.com/rjnw/scf.git/?path=scf-lib#a9405041f636ac7c4368b736d10f3f8a858eed74 \
    && raco pkg install --auto https://github.com/rjnw/sham.git/?path=sham-llvm#b4c1f1029a7b97de5c0c93f7399fdac38e4b5495 \
    && raco pkg install --auto https://github.com/rjnw/sham.git/?path=sham-lib#b4c1f1029a7b97de5c0c93f7399fdac38e4b5495
WORKDIR /dependency
COPY . .
WORKDIR /dependency/Dynamizer
RUN stack build && stack install --local-bin-path /usr/bin
WORKDIR /src
CMD ["/bin/bash"]
