#!/bin/bash
make -B  
EXPECT="OK"
ERROR=""
TRUE_OUT=""
TRUE_OUT1=""



strings=(
    "lattests201003/lattests/good"
    # "lattests201003/lattests/extensions/arrays1"
    "lattests201003/lattests/extensions/objects1"
    "lattests201003/lattests/extensions/objects2"
    "lattests201003/lattests/extensions/struct"
    # "mrjp-tests-master/good/arrays"
    "mrjp-tests-master/good/basic"
    ## "mrjp-tests-master/good/hardcore" #tych nie chcemy bo to na optymalizacje są
    # "mrjp-tests-master/good/virtual"
    # "mrjp-tests-master/gr5" #dziwna ta grupa5
)

for dir in "${strings[@]}"; do
    for filename in ${dir}/*.lat; do
        

        OUT=$( ( ./latc "$filename" ) 2> errFile)
        ERROR=$(<errFile)
        

        # ERROR=$( ( ./latc "$filename" ) 2>&1 )
        # OUTPUT=$(./latc "$filename")

        if [ "$EXPECT" != "$ERROR" ]
        then
            echo [ERROR] $filename 
            # echo $ERROR
        else
            gcc -m32 lib/runtime.o ${filename%%.*}.s -o ${filename%%.*}
            # ./${filename%%.*} > outFile

            if [ ! -f ${filename%%.*}.input ]; then
                TRUE_OUT=$( ( ./${filename%%.*} ) 2>&1 )
            else
                TRUE_OUT=$( ( cat ${filename%%.*}.input | ./${filename%%.*} ) 2>&1 )
            fi


            # # TRUE_OUT =$( ./${filename%%.*} )
            # TRUE_OUT =$(<outFile)
            EXPECT_OUT=$(<${filename%%.*}.output)

            
            if [ "$EXPECT_OUT" != "$TRUE_OUT" ]
            then
                echo $filename :OUT
                echo "--------expect------------------"
                echo "$EXPECT_OUT"
                echo "-----------true---------------"
                echo "$TRUE_OUT"
                echo "--------------------------"
                # echo $ERROR
            echo [ASM] $filename
            fi
            # echo [OK] $filename
        fi
        
        # if [ "$EXPECT_OUT" != "$OUT" ]
        # then
        #     echo $filename OUTTTTTT
        #     # echo $ERROR
        # fi
    done
done


for filename in lattests201003/lattests/bad/*.lat; do
    # echo $filename
    # ./latc "$filename"
    # echo ""


     ERROR=$( ( ./latc "$filename" ) 2>&1 )
        # OUTPUT=$(./latc "$filename")

        if [ "$EXPECT" == "$ERROR" ]
        then
            echo $filename
            # echo $ERROR
        fi
done
