#! /bin/bash

(cd simpleConcurrent/; javac ConcurrentArray.java)
jar cf SimpleConcurrent.jar simpleConcurrent/
# DEBUG=validation violat-validator simpleConcurrent/ConcurrentArray.json --jar SimpleConcurrent.jar --max-programs 1000 --maximality

