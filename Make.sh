#!/bin/bash

touch depend
coq_makefile SG_applpi_string.v SG_fs.v SG_applpi.v > Makefile.SG_server
make -f Makefile.SG_server depend
make -f Makefile.SG_server

