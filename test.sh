#!/bin/bash
 # && ./latc lattests201003/lattests/good/core032.lat

 make -B  
 EXPECT=""
 ERROR=""


strings=(
    "lattests201003/lattests/good"
    "lattests201003/lattests/extensions/arrays1"
    "lattests201003/lattests/extensions/objects1"
    "lattests201003/lattests/extensions/objects2"
    "lattests201003/lattests/extensions/struct"
    "mrjp-tests-master/good/arrays"
    "mrjp-tests-master/good/basic"
    "mrjp-tests-master/good/hardcore"
    "mrjp-tests-master/good/virtual"
    # "mrjp-tests-master/gr5" #dziwna ta grupa5
)

for dir in "${strings[@]}"; do
    for filename in ${dir}/*.lat; do
        
        ERROR=$( ( ./latc "$filename" ) 2>&1 )
        # OUTPUT=$(./latc "$filename")

        if [ "$EXPECT" != "$ERROR" ]
        then
            echo $filename
            # echo $ERROR
        fi
    done
done


for filename in lattests201003/lattests/bad/*.lat; do
    echo $filename
    ./latc "$filename"
    echo ""


    #  ERROR=$( ( ./latc "$filename" ) 2>&1 )
    #     # OUTPUT=$(./latc "$filename")

    #     if [ "$EXPECT" == "$ERROR" ]
    #     then
    #         echo $filename
    #         # echo $ERROR
    #     fi
done
