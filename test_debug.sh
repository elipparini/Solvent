#!/bin/bash

if [ "$#" -eq 2 ]; then
    folder_path="./examples"

    # Check if the folder exists
    if [ -d "$folder_path" ]; then
        # Use a for loop to iterate through files in the folder
        for file in $(ls -1 "$folder_path" | sort); do
            filename="$file"
            file="$folder_path/$file"
            echo -n -e "$(basename "$file")\t\t"
            start_time=$(date +%s.%N)
            python3 main.py $file $1 $2 > tests_autgen/$filename.py
            python3 main.py $file $1 $2 > output.py
            end_time=$(date +%s.%N)
            elapsed_time_compilation=$(echo "$end_time - $start_time" | bc)
            start_time=$(date +%s.%N)
            python3 output.py > .tmp
            end_time=$(date +%s.%N)
            elapsed_time_verification=$(echo "$end_time - $start_time" | bc)
            printf "\n\n\n\n"
            echo "$(cat .tmp)"
            echo " (Compilation time: $elapsed_time_compilation [sec], Verification time: $elapsed_time_verification [sec])"
            printf "\n\n\n\n"
        done
    else
        echo "Folder not found: $folder_path"
    fi
else
    echo "You have to pass two arguments: <number of transactions> <number of participants>"
fi