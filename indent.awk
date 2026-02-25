BEGIN {
    indent = 0
}

{
    # Check if line contains closing brace
    if ($0 ~ /ends/) {
        indent--
        if (indent < 0) indent = 0
    }
    
    # Print the line with current indentation
    for (i = 0; i < indent; i++) {
        printf "    "
    }
    print $0
    
    # Check if line contains opening brace
    if ($0 ~ /start/) {
        indent++
    }
}
