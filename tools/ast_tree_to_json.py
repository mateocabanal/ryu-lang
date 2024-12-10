import json
import re
import fileinput


def parse_rust_debug(input_str):
    lines = input_str.strip("\n").split("\n")
    stack = []  # Each element is a tuple (indent_level, current_dict)
    root = {}
    stack.append((-1, root))  # Initialize with root at indent -1

    for line_number, line in enumerate(lines, start=1):
        if not line.strip():
            continue  # Skip empty lines

        # Determine indentation level (number of leading spaces)
        indent = len(line) - len(line.lstrip(" "))
        content = line.strip()

        # Pop the stack to find the correct parent based on indentation
        while stack and indent <= stack[-1][0]:
            stack.pop()

        if not stack:
            raise ValueError(f"Invalid indentation at line {line_number}: {line}")

        parent = stack[-1][1]

        # Parse the line
        if "=" in content and not content.endswith(":"):
            # It's a key=value pair or node with attributes
            parts = content.split()
            node_label = parts[0]
            attributes = {}
            # NOTE: Check if this is a node with attributes
            if node_label.endswith(("Node", "DeclNode", "MethodNode", "FieldNode")):
                for attr in parts[1:]:
                    if "=" in attr:
                        k, v = map(str.strip, attr.split("=", 1))
                        attributes[k] = parse_value(v)
                if node_label == "FunctionDeclNode":
                    if "name" not in attributes:
                        raise ValueError(
                            f"FunctionDeclNode without a name at line {line_number}: {line}"
                        )
                    func_dict = attributes.copy()
                    # Initialize 'Functions' as a list if not present
                    if "Functions" not in parent:
                        parent["Functions"] = []
                    # Append each FunctionDeclNode as a separate dictionary
                    parent["Functions"].append({"FunctionDeclNode": func_dict})
                    # Push the function dict onto the stack to associate nested fields
                    stack.append((indent, func_dict))
                elif node_label == "ClassDeclNode":
                    if "name" not in attributes:
                        raise ValueError(
                            f"ClassDeclNode without a name at line {line_number}: {line}"
                        )
                    class_dict = attributes.copy()
                    # Initialize 'Classes' as a list if not present
                    if "Classes" not in parent:
                        parent["Classes"] = []
                    # Append each ClassDeclNode as a separate dictionary
                    parent["Classes"].append({"ClassDeclNode": class_dict})
                    # Push the class dict onto the stack to associate nested fields
                    stack.append((indent, class_dict))
                else:
                    # For other node types, handle normally
                    insert_into_parent(parent, node_label, attributes)
                    # Push to stack if it's a node that can have children
                    stack.append((indent, parent[node_label]))
            else:
                # It's a simple key=value pair
                key, value = map(str.strip, content.split("=", 1))
                parsed_value = parse_value(value)
                insert_into_parent(parent, key, parsed_value)
        elif ":" in content and not content.endswith(":"):
            # It's a key: value pair
            key, value = map(str.strip, content.split(":", 1))
            parsed_value = parse_value(value)
            insert_into_parent(parent, key, parsed_value)
        elif content.endswith(":"):
            # It's a key indicating a nested object
            key = content[:-1].strip()
            # Initialize nested dictionary
            nested = {}
            # Use insert_into_parent to handle parent being a list or dict
            insert_into_parent(parent, key, nested)
            # Push new context to stack
            stack.append((indent, nested))
        else:
            # It's a node with a single value or no value
            parts = content.split(None, 1)  # Split into node and the rest
            node_label = parts[0]
            if len(parts) == 2:
                # Node with a single value or attributes
                value_part = parts[1].strip()
                if "=" in value_part:
                    # It has attributes
                    attributes = {}
                    # Handle cases where key might contain spaces (e.g., "Arg 0")
                    # Use regex to split by key=value pairs
                    attr_matches = re.finditer(r'(\S+?)=("[^"]*"|\S+)', value_part)
                    for match in attr_matches:
                        k = match.group(1)
                        v = match.group(2)
                        attributes[k] = parse_value(v)
                    insert_into_parent(parent, node_label, attributes)
                    # Push to stack if it's a node that can have children
                    stack.append((indent, parent[node_label]))
                else:
                    # It's a single value
                    parsed_value = parse_value(value_part)
                    insert_into_parent(parent, node_label, parsed_value)
            else:
                # Node with no value, assign as empty dict
                insert_into_parent(parent, node_label, {})
                # Push new context to stack since it may have children
                if node_label in parent:
                    if isinstance(parent[node_label], list):
                        current_node = parent[node_label][-1]
                    else:
                        current_node = parent[node_label]
                    stack.append((indent, current_node))
    return root


def parse_value(value_str):
    """Parses a value string into appropriate JSON type, stripping Some() if present."""
    # Handle Some(value)
    some_match = re.match(r"^Some\((.*)\)$", value_str)
    if some_match:
        inner = some_match.group(1).strip()
        return parse_value(inner)
    if value_str.lower() == "none":
        return None
    elif value_str.startswith('"') and value_str.endswith('"'):
        return value_str[1:-1]
    else:
        # Try to convert to integer
        try:
            return int(value_str)
        except ValueError:
            pass
        # Try to convert to float
        try:
            return float(value_str)
        except ValueError:
            pass
        # Return as string
        return value_str


def insert_into_parent(parent, key, value):
    """Inserts a key-value pair into the parent dictionary, handling lists for repeated keys."""
    if isinstance(parent, list):
        # If parent is a list, assign the key-value pair to the last item in the list
        if len(parent) == 0:
            # No items yet, append a new dict
            parent.append({key: value})
        else:
            last_dict = parent[-1]
            if key in last_dict:
                if isinstance(last_dict[key], list):
                    last_dict[key].append(value)
                else:
                    last_dict[key] = [last_dict[key], value]
            else:
                last_dict[key] = value
    else:
        if key in parent:
            if isinstance(parent[key], list):
                parent[key].append(value)
            else:
                parent[key] = [parent[key], value]
        else:
            parent[key] = value


def main():
    rust_debug_output = ""
    for line in fileinput.input():
        rust_debug_output += line

    # Preprocess lines to convert '(no value)' to 'value=None'
    processed_lines = []
    for line in rust_debug_output.strip("\n").split("\n"):
        if "(no value)" in line:
            line = line.replace("(no value)", "value=None")
        processed_lines.append(line)
    processed_input = "\n".join(processed_lines)

    try:
        json_tree = parse_rust_debug(processed_input)
        json_output = json.dumps(json_tree, indent=2)
        print(json_output)
    except ValueError as ve:
        print(f"Error: {ve}")
    except TypeError as te:
        print(f"TypeError: {te}")


if __name__ == "__main__":
    main()
