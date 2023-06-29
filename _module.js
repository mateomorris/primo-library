function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}
function outro_and_destroy_block(block, lookup) {
    transition_out(block, 1, 1, () => {
        lookup.delete(block.key);
    });
}
function update_keyed_each(old_blocks, dirty, get_key, dynamic, ctx, list, lookup, node, destroy, create_each_block, next, get_context) {
    let o = old_blocks.length;
    let n = list.length;
    let i = o;
    const old_indexes = {};
    while (i--)
        old_indexes[old_blocks[i].key] = i;
    const new_blocks = [];
    const new_lookup = new Map();
    const deltas = new Map();
    const updates = [];
    i = n;
    while (i--) {
        const child_ctx = get_context(ctx, list, i);
        const key = get_key(child_ctx);
        let block = lookup.get(key);
        if (!block) {
            block = create_each_block(key, child_ctx);
            block.c();
        }
        else if (dynamic) {
            // defer updates until all the DOM shuffling is done
            updates.push(() => block.p(child_ctx, dirty));
        }
        new_lookup.set(key, new_blocks[i] = block);
        if (key in old_indexes)
            deltas.set(key, Math.abs(i - old_indexes[key]));
    }
    const will_move = new Set();
    const did_move = new Set();
    function insert(block) {
        transition_in(block, 1);
        block.m(node, next);
        lookup.set(block.key, block);
        next = block.first;
        n--;
    }
    while (o && n) {
        const new_block = new_blocks[n - 1];
        const old_block = old_blocks[o - 1];
        const new_key = new_block.key;
        const old_key = old_block.key;
        if (new_block === old_block) {
            // do nothing
            next = new_block.first;
            o--;
            n--;
        }
        else if (!new_lookup.has(old_key)) {
            // remove old block
            destroy(old_block, lookup);
            o--;
        }
        else if (!lookup.has(new_key) || will_move.has(new_key)) {
            insert(new_block);
        }
        else if (did_move.has(old_key)) {
            o--;
        }
        else if (deltas.get(new_key) > deltas.get(old_key)) {
            did_move.add(new_key);
            insert(new_block);
        }
        else {
            will_move.add(old_key);
            o--;
        }
    }
    while (o--) {
        const old_block = old_blocks[o];
        if (!new_lookup.has(old_block.key))
            destroy(old_block, lookup);
    }
    while (n)
        insert(new_blocks[n - 1]);
    run_all(updates);
    return new_blocks;
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta;
	let style;
	let t;

	return {
		c() {
			meta = element("meta");
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: black;\n  --color-white: white;\n  --color-background: #121212;\n  --color-body: #222;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #cbcace;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: var(--color-body, #222);\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n  line-height: 1.2;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  padding: 5rem 2rem;\n  margin: 0 auto;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid var(--color-accent, black);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1;\n  font-weight: 600;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 5px;\n  padding: 12px 20px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  font-size: 1rem;\n  font-weight: 400;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 2.5rem;\n    line-height: 1;\n    font-weight: 600;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.5rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1ka484s', document.head);
			meta = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: black;\n  --color-white: white;\n  --color-background: #121212;\n  --color-body: #222;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #cbcace;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: var(--color-body, #222);\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: white;\n  line-height: 1.2;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  padding: 5rem 2rem;\n  margin: 0 auto;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 500;\n  border-bottom: 2px solid var(--color-accent, black);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1;\n  font-weight: 600;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 5px;\n  padding: 12px 20px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  font-size: 1rem;\n  font-weight: 400;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.section .content a.link {\n  }\n.section .content h1 {\n    font-size: 2.5rem;\n    line-height: 1;\n    font-weight: 600;\n    margin-bottom: 1rem;\n  }\n.section .content h2 {\n    font-size: 2rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.section .content h3 {\n    font-size: 1.5rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta, "name", "viewport");
			attr(meta, "content", "width=device-width, initial-scale=1");
		},
		m(target, anchor) {
			append_hydration(document.head, meta);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta);
			detach(style);
		}
	};
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[2].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[2].url);
			attr(a, "class", "button svelte-1qk24ik");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*link*/ 4 && t_value !== (t_value = /*link*/ ctx[2].label + "")) set_data(t, t_value);

			if (dirty & /*link*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$1(ctx) {
	let div3;
	let section;
	let div2;
	let div1;
	let h1;
	let t0;
	let t1;
	let div0;
	let t2;
	let t3;
	let t4;
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let if_block = /*link*/ ctx[2].label && create_if_block(ctx);

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div1 = element("div");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			if (if_block) if_block.c();
			t4 = space();
			figure = element("figure");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h1 = claim_element(div1_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t2 = claim_text(div0_nodes, /*subheading*/ ctx[1]);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			figure = claim_element(div2_nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { src: true, alt: true, class: true });
			figure_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-1qk24ik");
			attr(div0, "class", "subheading svelte-1qk24ik");
			attr(div1, "class", "body svelte-1qk24ik");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[3].alt);
			attr(img, "class", "svelte-1qk24ik");
			attr(figure, "class", "svelte-1qk24ik");
			attr(div2, "class", "section-container svelte-1qk24ik");
			attr(section, "class", "svelte-1qk24ik");
			toggle_class(section, "image-left", /*variation*/ ctx[4] === "image_left");
			attr(div3, "class", "section");
			attr(div3, "id", "section-b03543d2");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div1);
			append_hydration(div1, h1);
			append_hydration(h1, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, t2);
			append_hydration(div1, t3);
			if (if_block) if_block.m(div1, null);
			append_hydration(div2, t4);
			append_hydration(div2, figure);
			append_hydration(figure, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (/*link*/ ctx[2].label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(div1, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*image*/ 8 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 8 && img_alt_value !== (img_alt_value = /*image*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*variation*/ 16) {
				toggle_class(section, "image-left", /*variation*/ ctx[4] === "image_left");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
			if (if_block) if_block.d();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { link } = $$props;
	let { image } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('image' in $$props) $$invalidate(3, image = $$props.image);
		if ('variation' in $$props) $$invalidate(4, variation = $$props.variation);
	};

	return [heading, subheading, link, image, variation];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment$1, safe_not_equal, {
			heading: 0,
			subheading: 1,
			link: 2,
			image: 3,
			variation: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].image;
	return child_ctx;
}

// (32:6) {#each items as {image}}
function create_each_block(ctx) {
	let div;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;

	return {
		c() {
			div = element("div");
			img = element("img");
			t = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			img = claim_element(div_nodes, "IMG", { src: true, alt: true });
			t = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(div, "class", "item svelte-1s5lign");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, img);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let section;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", {});
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1s5lign");
			attr(div0, "class", "items svelte-1s5lign");
			attr(div1, "class", "section-container");
			attr(div2, "class", "section");
			attr(div2, "id", "section-8dbafac8");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$2, safe_not_equal, { heading: 0, items: 1 });
	}
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block$1(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$3(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block$1(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$3, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i];
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].link;
	child_ctx[6] = list[i].icon;
	return child_ctx;
}

// (96:6) {#if person.image.url}
function create_if_block$2(ctx) {
	let figure;
	let img;
	let img_alt_value;
	let img_src_value;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { alt: true, src: true, class: true });
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "alt", img_alt_value = /*person*/ ctx[2].image.alt);
			if (!src_url_equal(img.src, img_src_value = /*person*/ ctx[2].image.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-7tm6a9");
			attr(figure, "class", "svelte-7tm6a9");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
		},
		p(ctx, dirty) {
			if (dirty & /*people*/ 2 && img_alt_value !== (img_alt_value = /*person*/ ctx[2].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*people*/ 2 && !src_url_equal(img.src, img_src_value = /*person*/ ctx[2].image.url)) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(figure);
		}
	};
}

// (107:10) {#each person.social_links as {link, icon}}
function create_each_block_1(ctx) {
	let a;
	let icon;
	let t;
	let a_href_value;
	let a_aria_label_value;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[6] } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[5].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[5].label);
			attr(a, "class", "svelte-7tm6a9");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*people*/ 2) icon_changes.icon = /*icon*/ ctx[6];
			icon.$set(icon_changes);

			if (!current || dirty & /*people*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[5].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*people*/ 2 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[5].label)) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (94:4) {#each people as person}
function create_each_block$1(ctx) {
	let li;
	let t0;
	let div2;
	let div0;
	let span0;
	let t1_value = /*person*/ ctx[2].name + "";
	let t1;
	let t2;
	let span1;
	let t3_value = /*person*/ ctx[2].title + "";
	let t3;
	let t4;
	let div1;
	let t5;
	let current;
	let if_block = /*person*/ ctx[2].image.url && create_if_block$2(ctx);
	let each_value_1 = /*person*/ ctx[2].social_links;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			li = element("li");
			if (if_block) if_block.c();
			t0 = space();
			div2 = element("div");
			div0 = element("div");
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			if (if_block) if_block.l(li_nodes);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "name svelte-7tm6a9");
			attr(span1, "class", "title svelte-7tm6a9");
			attr(div0, "class", "details svelte-7tm6a9");
			attr(div1, "class", "social svelte-7tm6a9");
			attr(div2, "class", "info");
			attr(li, "class", "svelte-7tm6a9");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, span1);
			append_hydration(span1, t3);
			append_hydration(div2, t4);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(li, t5);
			current = true;
		},
		p(ctx, dirty) {
			if (/*person*/ ctx[2].image.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(li, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if ((!current || dirty & /*people*/ 2) && t1_value !== (t1_value = /*person*/ ctx[2].name + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*people*/ 2) && t3_value !== (t3_value = /*person*/ ctx[2].title + "")) set_data(t3, t3_value);

			if (dirty & /*people*/ 2) {
				each_value_1 = /*person*/ ctx[2].social_links;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$4(ctx) {
	let div;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let current;
	let each_value = /*people*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-7tm6a9");
			attr(ul, "class", "cards svelte-7tm6a9");
			attr(section, "class", "section-container svelte-7tm6a9");
			attr(div, "class", "section");
			attr(div, "id", "section-8e68f357");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*people*/ 2) {
				each_value = /*people*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { people } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('people' in $$props) $$invalidate(1, people = $$props.people);
	};

	return [heading, people];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$3, create_fragment$4, safe_not_equal, { heading: 0, people: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i];
	return child_ctx;
}

// (50:4) {#each cards as card}
function create_each_block$2(ctx) {
	let li;
	let h3;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*card*/ ctx[2].title + "";
	let t1;
	let t2;
	let div;
	let raw_value = /*card*/ ctx[2].description.html + "";
	let t3;
	let current;

	icon = new Component$3({
			props: {
				icon: /*card*/ ctx[2].icon,
				width: "22",
				height: "22",
				style: "color: var(--color-accent, rebeccapurple)"
			}
		});

	return {
		c() {
			li = element("li");
			h3 = element("h3");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			div = element("div");
			t3 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			h3 = claim_element(li_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			span0 = claim_element(h3_nodes, "SPAN", {});
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(h3_nodes);
			span1 = claim_element(h3_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			h3_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			div = claim_element(li_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			t3 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span1, "class", "label svelte-sqs4td");
			attr(h3, "class", "title svelte-sqs4td");
			attr(div, "class", "description");
			attr(li, "class", "svelte-sqs4td");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, h3);
			append_hydration(h3, span0);
			mount_component(icon, span0, null);
			append_hydration(h3, t0);
			append_hydration(h3, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			append_hydration(li, div);
			div.innerHTML = raw_value;
			append_hydration(li, t3);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*cards*/ 2) icon_changes.icon = /*card*/ ctx[2].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*cards*/ 2) && t1_value !== (t1_value = /*card*/ ctx[2].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 2) && raw_value !== (raw_value = /*card*/ ctx[2].description.html + "")) div.innerHTML = raw_value;		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$5(ctx) {
	let div;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let current;
	let each_value = /*cards*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-sqs4td");
			attr(ul, "class", "svelte-sqs4td");
			attr(section, "class", "section-container svelte-sqs4td");
			attr(div, "class", "section");
			attr(div, "id", "section-470554db");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*cards*/ 2) {
				each_value = /*cards*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('cards' in $$props) $$invalidate(1, cards = $$props.cards);
	};

	return [heading, cards];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$5, safe_not_equal, { heading: 0, cards: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	child_ctx[4] = list[i].icon;
	return child_ctx;
}

// (76:4) {#if email}
function create_if_block$3(ctx) {
	let a;
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(/*email*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, /*email*/ ctx[1]);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-fjx86h");
			attr(a, "href", a_href_value = "mailto:" + /*email*/ ctx[1]);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*email*/ 2) set_data(t, /*email*/ ctx[1]);

			if (dirty & /*email*/ 2 && a_href_value !== (a_href_value = "mailto:" + /*email*/ ctx[1])) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (80:6) {#each social as {link, icon}}
function create_each_block$3(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[3].label);
			attr(a, "class", "svelte-fjx86h");
			attr(li, "class", "svelte-fjx86h");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 4) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 4 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[3].label)) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$6(ctx) {
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let t2;
	let ul;
	let current;
	let if_block = /*email*/ ctx[1] && create_if_block$3(ctx);
	let each_value = /*social*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			if (if_block) if_block.l(div0_nodes);
			t2 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-fjx86h");
			attr(ul, "class", "svelte-fjx86h");
			attr(div0, "class", "card svelte-fjx86h");
			attr(section, "class", "section-container svelte-fjx86h");
			attr(div1, "class", "section");
			attr(div1, "id", "section-40e73c7f");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			if (if_block) if_block.m(div0, null);
			append_hydration(div0, t2);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (/*email*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$3(ctx);
					if_block.c();
					if_block.m(div0, t2);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*social*/ 4) {
				each_value = /*social*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { email } = $$props;
	let { social } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('email' in $$props) $$invalidate(1, email = $$props.email);
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
	};

	return [heading, email, social];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$6, safe_not_equal, { heading: 0, email: 1, social: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (50:6) {#each buttons as button}
function create_each_block$4(ctx) {
	let a;
	let icon;
	let t0;
	let span;
	let t1_value = /*button*/ ctx[3].link.label + "";
	let t1;
	let t2;
	let a_href_value;
	let current;
	icon = new Component$3({ props: { icon: /*button*/ ctx[3].icon } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t0 = space();
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t0 = claim_space(a_nodes);
			span = claim_element(a_nodes, "SPAN", {});
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-o9z257");
			attr(a, "href", a_href_value = /*button*/ ctx[3].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t0);
			append_hydration(a, span);
			append_hydration(span, t1);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*buttons*/ 4) icon_changes.icon = /*button*/ ctx[3].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*buttons*/ 4) && t1_value !== (t1_value = /*button*/ ctx[3].link.label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*buttons*/ 4 && a_href_value !== (a_href_value = /*button*/ ctx[3].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$7(ctx) {
	let div3;
	let section;
	let div2;
	let h2;
	let t0;
	let t1;
	let div0;
	let raw_value = /*body*/ ctx[1].html + "";
	let t2;
	let div1;
	let current;
	let each_value = /*buttons*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$4(get_each_context$4(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h2 = claim_element(div2_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-o9z257");
			attr(div0, "class", "body svelte-o9z257");
			attr(div1, "class", "buttons svelte-o9z257");
			attr(div2, "class", "card svelte-o9z257");
			attr(section, "class", "section-container svelte-o9z257");
			attr(div3, "class", "section");
			attr(div3, "id", "section-9574c6f1");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, h2);
			append_hydration(h2, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t2);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if ((!current || dirty & /*body*/ 2) && raw_value !== (raw_value = /*body*/ ctx[1].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*buttons*/ 4) {
				each_value = /*buttons*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$4(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$4(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { body } = $$props;
	let { buttons } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('body' in $$props) $$invalidate(1, body = $$props.body);
		if ('buttons' in $$props) $$invalidate(2, buttons = $$props.buttons);
	};

	return [heading, body, buttons];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$7, safe_not_equal, { heading: 0, body: 1, buttons: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div2;
	let section;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let raw_value = /*body*/ ctx[1].html + "";
	let t2;
	let form_1;
	let label;
	let span;
	let t3_value = /*form*/ ctx[2].input_label + "";
	let t3;
	let t4;
	let input;
	let t5;
	let button;
	let t6_value = /*form*/ ctx[2].submit_label + "";
	let t6;
	let mounted;
	let dispose;

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			form_1 = element("form");
			label = element("label");
			span = element("span");
			t3 = text(t3_value);
			t4 = space();
			input = element("input");
			t5 = space();
			button = element("button");
			t6 = text(t6_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			form_1 = claim_element(section_nodes, "FORM", { class: true });
			var form_1_nodes = children(form_1);
			label = claim_element(form_1_nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", {});
			var span_nodes = children(span);
			t3 = claim_text(span_nodes, t3_value);
			span_nodes.forEach(detach);
			t4 = claim_space(label_nodes);
			input = claim_element(label_nodes, "INPUT", { type: true, class: true });
			label_nodes.forEach(detach);
			t5 = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t6 = claim_text(button_nodes, t6_value);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-rlqomu");
			attr(div0, "class", "body svelte-rlqomu");
			attr(div1, "class", "content svelte-rlqomu");
			attr(input, "type", "email");
			attr(input, "class", "svelte-rlqomu");
			attr(label, "class", "svelte-rlqomu");
			attr(button, "type", "submit");
			attr(button, "class", "button svelte-rlqomu");
			attr(form_1, "class", "svelte-rlqomu");
			attr(section, "class", "section-container svelte-rlqomu");
			attr(div2, "class", "section");
			attr(div2, "id", "section-0d7dec4b");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(section, t2);
			append_hydration(section, form_1);
			append_hydration(form_1, label);
			append_hydration(label, span);
			append_hydration(span, t3);
			append_hydration(label, t4);
			append_hydration(label, input);
			append_hydration(form_1, t5);
			append_hydration(form_1, button);
			append_hydration(button, t6);

			if (!mounted) {
				dispose = listen(form_1, "submit", prevent_default(/*submit_handler*/ ctx[3]));
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*body*/ 2 && raw_value !== (raw_value = /*body*/ ctx[1].html + "")) div0.innerHTML = raw_value;			if (dirty & /*form*/ 4 && t3_value !== (t3_value = /*form*/ ctx[2].input_label + "")) set_data(t3, t3_value);
			if (dirty & /*form*/ 4 && t6_value !== (t6_value = /*form*/ ctx[2].submit_label + "")) set_data(t6, t6_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			mounted = false;
			dispose();
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { body } = $$props;
	let { form } = $$props;

	const submit_handler = ({ target }) => {
		const data = new FormData(target); // send `data` to email service
	};

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('body' in $$props) $$invalidate(1, body = $$props.body);
		if ('form' in $$props) $$invalidate(2, form = $$props.form);
	};

	return [heading, body, form, submit_handler];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, create_fragment$8, safe_not_equal, { heading: 0, body: 1, form: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	child_ctx[7] = i;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	child_ctx[9] = list[i].icon;
	return child_ctx;
}

// (94:6) {#each social as { link, icon }}
function create_each_block_1$1(ctx) {
	let a;
	let span;
	let icon;
	let t0;
	let t1_value = /*link*/ ctx[8].label + "";
	let t1;
	let t2;
	let a_href_value;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[9] } });

	return {
		c() {
			a = element("a");
			span = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			claim_component(icon.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			t0 = claim_space(a_nodes);
			t1 = claim_text(a_nodes, t1_value);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "icon svelte-15f55d3");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(a, "class", "svelte-15f55d3");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			mount_component(icon, span, null);
			append_hydration(a, t0);
			append_hydration(a, t1);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 4) icon_changes.icon = /*icon*/ ctx[9];
			icon.$set(icon_changes);
			if ((!current || dirty & /*social*/ 4) && t1_value !== (t1_value = /*link*/ ctx[8].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*social*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (111:6) {:else}
function create_else_block$1(ctx) {
	let label;
	let span;
	let t0_value = /*input*/ ctx[5].label + "";
	let t0;
	let t1;
	let input;
	let input_type_value;
	let input_placeholder_value;

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(label_nodes);

			input = claim_element(label_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-15f55d3");
			attr(input, "type", input_type_value = /*input*/ ctx[5].type || "text");
			attr(input, "placeholder", input_placeholder_value = /*input*/ ctx[5].placeholder);
			attr(input, "class", "svelte-15f55d3");
			attr(label, "class", "svelte-15f55d3");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(label, t1);
			append_hydration(label, input);
		},
		p(ctx, dirty) {
			if (dirty & /*inputs*/ 8 && t0_value !== (t0_value = /*input*/ ctx[5].label + "")) set_data(t0, t0_value);

			if (dirty & /*inputs*/ 8 && input_type_value !== (input_type_value = /*input*/ ctx[5].type || "text")) {
				attr(input, "type", input_type_value);
			}

			if (dirty & /*inputs*/ 8 && input_placeholder_value !== (input_placeholder_value = /*input*/ ctx[5].placeholder)) {
				attr(input, "placeholder", input_placeholder_value);
			}
		},
		d(detaching) {
			if (detaching) detach(label);
		}
	};
}

// (106:6) {#if input.type === "textarea"}
function create_if_block$4(ctx) {
	let label;
	let span;
	let t0_value = /*input*/ ctx[5].label + "";
	let t0;
	let t1;
	let textarea;

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			textarea = element("textarea");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(label_nodes);
			textarea = claim_element(label_nodes, "TEXTAREA", { class: true });
			children(textarea).forEach(detach);
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-15f55d3");
			attr(textarea, "class", "svelte-15f55d3");
			attr(label, "class", "svelte-15f55d3");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(label, t1);
			append_hydration(label, textarea);
		},
		p(ctx, dirty) {
			if (dirty & /*inputs*/ 8 && t0_value !== (t0_value = /*input*/ ctx[5].label + "")) set_data(t0, t0_value);
		},
		d(detaching) {
			if (detaching) detach(label);
		}
	};
}

// (105:4) {#each inputs as input, i}
function create_each_block$5(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*input*/ ctx[5].type === "textarea") return create_if_block$4;
		return create_else_block$1;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment$9(ctx) {
	let div3;
	let section;
	let div2;
	let h2;
	let t0;
	let t1;
	let div0;
	let t2;
	let div1;
	let t3;
	let form;
	let t4;
	let button;
	let t5;
	let current;
	let each_value_1 = /*social*/ ctx[2];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks_1[i], 1, 1, () => {
		each_blocks_1[i] = null;
	});

	let each_value = /*inputs*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$5(get_each_context$5(ctx, each_value, i));
	}

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t3 = space();
			form = element("form");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			button = element("button");
			t5 = text(/*submit_label*/ ctx[4]);
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h2 = claim_element(div2_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			form = claim_element(section_nodes, "FORM", { class: true });
			var form_nodes = children(form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(form_nodes);
			}

			t4 = claim_space(form_nodes);
			button = claim_element(form_nodes, "BUTTON", { class: true, type: true });
			var button_nodes = children(button);
			t5 = claim_text(button_nodes, /*submit_label*/ ctx[4]);
			button_nodes.forEach(detach);
			form_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(div0, "class", "body svelte-15f55d3");
			attr(div1, "class", "social-links svelte-15f55d3");
			attr(div2, "class", "content svelte-15f55d3");
			attr(button, "class", "button svelte-15f55d3");
			attr(button, "type", "submit");
			attr(form, "class", "svelte-15f55d3");
			attr(section, "class", "section-container svelte-15f55d3");
			attr(div3, "class", "section");
			attr(div3, "id", "section-c904e71f");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, h2);
			append_hydration(h2, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div0);
			div0.innerHTML = /*subheading*/ ctx[1];
			append_hydration(div2, t2);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div1, null);
				}
			}

			append_hydration(section, t3);
			append_hydration(section, form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(form, null);
				}
			}

			append_hydration(form, t4);
			append_hydration(form, button);
			append_hydration(button, t5);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (!current || dirty & /*subheading*/ 2) div0.innerHTML = /*subheading*/ ctx[1];
			if (dirty & /*social*/ 4) {
				each_value_1 = /*social*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
						transition_in(each_blocks_1[i], 1);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						transition_in(each_blocks_1[i], 1);
						each_blocks_1[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks_1.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (dirty & /*inputs*/ 8) {
				each_value = /*inputs*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$5(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$5(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(form, t4);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (!current || dirty & /*submit_label*/ 16) set_data(t5, /*submit_label*/ ctx[4]);
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks_1[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks_1 = each_blocks_1.filter(Boolean);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				transition_out(each_blocks_1[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { social } = $$props;
	let { inputs } = $$props;
	let { submit_label } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
		if ('inputs' in $$props) $$invalidate(3, inputs = $$props.inputs);
		if ('submit_label' in $$props) $$invalidate(4, submit_label = $$props.submit_label);
	};

	return [heading, subheading, social, inputs, submit_label];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$9, safe_not_equal, {
			heading: 0,
			subheading: 1,
			social: 2,
			inputs: 3,
			submit_label: 4
		});
	}
}

function cubicOut(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}
function slide(node, { delay = 0, duration = 400, easing = cubicOut, axis = 'y' } = {}) {
    const style = getComputedStyle(node);
    const opacity = +style.opacity;
    const primary_property = axis === 'y' ? 'height' : 'width';
    const primary_property_value = parseFloat(style[primary_property]);
    const secondary_properties = axis === 'y' ? ['top', 'bottom'] : ['left', 'right'];
    const capitalized_secondary_properties = secondary_properties.map((e) => `${e[0].toUpperCase()}${e.slice(1)}`);
    const padding_start_value = parseFloat(style[`padding${capitalized_secondary_properties[0]}`]);
    const padding_end_value = parseFloat(style[`padding${capitalized_secondary_properties[1]}`]);
    const margin_start_value = parseFloat(style[`margin${capitalized_secondary_properties[0]}`]);
    const margin_end_value = parseFloat(style[`margin${capitalized_secondary_properties[1]}`]);
    const border_width_start_value = parseFloat(style[`border${capitalized_secondary_properties[0]}Width`]);
    const border_width_end_value = parseFloat(style[`border${capitalized_secondary_properties[1]}Width`]);
    return {
        delay,
        duration,
        easing,
        css: t => 'overflow: hidden;' +
            `opacity: ${Math.min(t * 20, 1) * opacity};` +
            `${primary_property}: ${t * primary_property_value}px;` +
            `padding-${secondary_properties[0]}: ${t * padding_start_value}px;` +
            `padding-${secondary_properties[1]}: ${t * padding_end_value}px;` +
            `margin-${secondary_properties[0]}: ${t * margin_start_value}px;` +
            `margin-${secondary_properties[1]}: ${t * margin_end_value}px;` +
            `border-${secondary_properties[0]}-width: ${t * border_width_start_value}px;` +
            `border-${secondary_properties[1]}-width: ${t * border_width_end_value}px;`
    };
}

/* generated by Svelte v3.58.0 */

function create_key_block(ctx) {
	let div2;
	let span0;
	let icon;
	let t0;
	let div0;
	let raw_value = /*activeItem*/ ctx[3].quote.html + "";
	let div0_data_key_value;
	let t1;
	let div1;
	let span1;
	let t2_value = /*activeItem*/ ctx[3].name + "";
	let t2;
	let span1_data_key_value;
	let t3;
	let span2;
	let t4_value = /*activeItem*/ ctx[3].title + "";
	let t4;
	let span2_data_key_value;
	let div2_intro;
	let current;
	icon = new Component$3({ props: { icon: "fa6-solid:quote-right" } });

	return {
		c() {
			div2 = element("div");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			div0 = element("div");
			t1 = space();
			div1 = element("div");
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span2 = element("span");
			t4 = text(t4_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			span0 = claim_element(div2_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true, "data-key": true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span1 = claim_element(div1_nodes, "SPAN", { class: true, "data-key": true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			span2 = claim_element(div1_nodes, "SPAN", { class: true, "data-key": true });
			var span2_nodes = children(span2);
			t4 = claim_text(span2_nodes, t4_value);
			span2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "quote-icon svelte-1rjok2w");
			attr(div0, "class", "quote svelte-1rjok2w");
			attr(div0, "data-key", div0_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].quote");
			attr(span1, "class", "name svelte-1rjok2w");
			attr(span1, "data-key", span1_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].name");
			attr(span2, "class", "title svelte-1rjok2w");
			attr(span2, "data-key", span2_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].title");
			attr(div1, "class", "person svelte-1rjok2w");
			attr(div2, "class", "card svelte-1rjok2w");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, span0);
			mount_component(icon, span0, null);
			append_hydration(div2, t0);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, span1);
			append_hydration(span1, t2);
			append_hydration(div1, t3);
			append_hydration(div1, span2);
			append_hydration(span2, t4);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*activeItem*/ 8) && raw_value !== (raw_value = /*activeItem*/ ctx[3].quote.html + "")) div0.innerHTML = raw_value;
			if (!current || dirty & /*activeIndex*/ 4 && div0_data_key_value !== (div0_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].quote")) {
				attr(div0, "data-key", div0_data_key_value);
			}

			if ((!current || dirty & /*activeItem*/ 8) && t2_value !== (t2_value = /*activeItem*/ ctx[3].name + "")) set_data(t2, t2_value);

			if (!current || dirty & /*activeIndex*/ 4 && span1_data_key_value !== (span1_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].name")) {
				attr(span1, "data-key", span1_data_key_value);
			}

			if ((!current || dirty & /*activeItem*/ 8) && t4_value !== (t4_value = /*activeItem*/ ctx[3].title + "")) set_data(t4, t4_value);

			if (!current || dirty & /*activeIndex*/ 4 && span2_data_key_value !== (span2_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].title")) {
				attr(span2, "data-key", span2_data_key_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			if (!div2_intro) {
				add_render_callback(() => {
					div2_intro = create_in_transition(div2, fade, {});
					div2_intro.start();
				});
			}

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_component(icon);
		}
	};
}

// (109:4) {#if testimonials.length > 1}
function create_if_block$5(ctx) {
	let div;
	let button0;
	let icon0;
	let button0_disabled_value;
	let t;
	let button1;
	let icon1;
	let button1_disabled_value;
	let current;
	let mounted;
	let dispose;
	icon0 = new Component$3({ props: { icon: "charm:chevron-left" } });
	icon1 = new Component$3({ props: { icon: "charm:chevron-right" } });

	return {
		c() {
			div = element("div");
			button0 = element("button");
			create_component(icon0.$$.fragment);
			t = space();
			button1 = element("button");
			create_component(icon1.$$.fragment);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			button0 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button0_nodes = children(button0);
			claim_component(icon0.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t = claim_space(div_nodes);
			button1 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button1_nodes = children(button1);
			claim_component(icon1.$$.fragment, button1_nodes);
			button1_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			button0.disabled = button0_disabled_value = /*activeIndex*/ ctx[2] === 0;
			attr(button0, "aria-label", "Show previous item");
			attr(button0, "class", "svelte-1rjok2w");
			button1.disabled = button1_disabled_value = /*activeIndex*/ ctx[2] >= /*testimonials*/ ctx[1].length - 1;
			attr(button1, "aria-label", "Show next item");
			attr(button1, "class", "svelte-1rjok2w");
			attr(div, "class", "controls svelte-1rjok2w");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, button0);
			mount_component(icon0, button0, null);
			append_hydration(div, t);
			append_hydration(div, button1);
			mount_component(icon1, button1, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*showPreviousItem*/ ctx[4]),
					listen(button1, "click", /*showNextItem*/ ctx[5])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*activeIndex*/ 4 && button0_disabled_value !== (button0_disabled_value = /*activeIndex*/ ctx[2] === 0)) {
				button0.disabled = button0_disabled_value;
			}

			if (!current || dirty & /*activeIndex, testimonials*/ 6 && button1_disabled_value !== (button1_disabled_value = /*activeIndex*/ ctx[2] >= /*testimonials*/ ctx[1].length - 1)) {
				button1.disabled = button1_disabled_value;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon0);
			destroy_component(icon1);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$a(ctx) {
	let div1;
	let aside;
	let h2;
	let t0;
	let t1;
	let div0;
	let previous_key = /*activeIndex*/ ctx[2];
	let t2;
	let current;
	let key_block = create_key_block(ctx);
	let if_block = /*testimonials*/ ctx[1].length > 1 && create_if_block$5(ctx);

	return {
		c() {
			div1 = element("div");
			aside = element("aside");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			key_block.c();
			t2 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			aside = claim_element(div1_nodes, "ASIDE", { class: true });
			var aside_nodes = children(aside);
			h2 = claim_element(aside_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(aside_nodes);
			div0 = claim_element(aside_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			key_block.l(div0_nodes);
			t2 = claim_space(div0_nodes);
			if (if_block) if_block.l(div0_nodes);
			div0_nodes.forEach(detach);
			aside_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1rjok2w");
			attr(div0, "class", "testimonial svelte-1rjok2w");
			attr(aside, "class", "section-container svelte-1rjok2w");
			attr(div1, "class", "section");
			attr(div1, "id", "section-35966b7b");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, aside);
			append_hydration(aside, h2);
			append_hydration(h2, t0);
			append_hydration(aside, t1);
			append_hydration(aside, div0);
			key_block.m(div0, null);
			append_hydration(div0, t2);
			if (if_block) if_block.m(div0, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*activeIndex*/ 4 && safe_not_equal(previous_key, previous_key = /*activeIndex*/ ctx[2])) {
				group_outros();
				transition_out(key_block, 1, 1, noop);
				check_outros();
				key_block = create_key_block(ctx);
				key_block.c();
				transition_in(key_block, 1);
				key_block.m(div0, t2);
			} else {
				key_block.p(ctx, dirty);
			}

			if (/*testimonials*/ ctx[1].length > 1) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*testimonials*/ 2) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$5(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div0, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(key_block);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(key_block);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			key_block.d(detaching);
			if (if_block) if_block.d();
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let activeItem;
	let { heading } = $$props;
	let { testimonials } = $$props;
	let activeIndex = 0;

	function showPreviousItem() {
		$$invalidate(2, activeIndex = activeIndex - 1);
	}

	function showNextItem() {
		$$invalidate(2, activeIndex = activeIndex + 1);
	}

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('testimonials' in $$props) $$invalidate(1, testimonials = $$props.testimonials);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*testimonials, activeIndex*/ 6) {
			 $$invalidate(3, activeItem = testimonials[activeIndex]);
		}
	};

	return [heading, testimonials, activeIndex, activeItem, showPreviousItem, showNextItem];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, create_fragment$a, safe_not_equal, { heading: 0, testimonials: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$6(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	child_ctx[5] = i;
	return child_ctx;
}

function get_each_context_1$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].item;
	child_ctx[7] = list[i].icon;
	child_ctx[9] = i;
	return child_ctx;
}

// (107:10) {#each tier.features as { item, icon }
function create_each_block_1$2(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*item*/ ctx[6] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[7] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", {});
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-eigrhe");
			attr(li, "class", "svelte-eigrhe");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*tiers*/ 4) icon_changes.icon = /*icon*/ ctx[7];
			icon.$set(icon_changes);
			if ((!current || dirty & /*tiers*/ 4) && t1_value !== (t1_value = /*item*/ ctx[6] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (116:8) {#if tier.link.label}
function create_if_block$6(ctx) {
	let a;
	let t_value = /*tier*/ ctx[3].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*tier*/ ctx[3].link.url);
			attr(a, "class", "button svelte-eigrhe");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*tiers*/ 4 && t_value !== (t_value = /*tier*/ ctx[3].link.label + "")) set_data(t, t_value);

			if (dirty & /*tiers*/ 4 && a_href_value !== (a_href_value = /*tier*/ ctx[3].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (95:4) {#each tiers as tier, tier_index}
function create_each_block$6(ctx) {
	let div1;
	let header;
	let h3;
	let t0_value = /*tier*/ ctx[3].title + "";
	let t0;
	let t1;
	let div0;
	let span0;
	let t2_value = /*tier*/ ctx[3].price.numerator + "";
	let t2;
	let t3;
	let span1;
	let t4_value = /*tier*/ ctx[3].price.denominator + "";
	let t4;
	let t5;
	let span2;
	let raw_value = /*tier*/ ctx[3].description.html + "";
	let t6;
	let hr;
	let t7;
	let ul;
	let t8;
	let t9;
	let current;
	let each_value_1 = /*tier*/ ctx[3].features;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$2(get_each_context_1$2(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block = /*tier*/ ctx[3].link.label && create_if_block$6(ctx);

	return {
		c() {
			div1 = element("div");
			header = element("header");
			h3 = element("h3");
			t0 = text(t0_value);
			t1 = space();
			div0 = element("div");
			span0 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span1 = element("span");
			t4 = text(t4_value);
			t5 = space();
			span2 = element("span");
			t6 = space();
			hr = element("hr");
			t7 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			if (if_block) if_block.c();
			t9 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, t0_value);
			h3_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t2 = claim_text(span0_nodes, t2_value);
			span0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, t4_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(header_nodes);
			span2 = claim_element(header_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			span2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			hr = claim_element(div1_nodes, "HR", { class: true });
			t7 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			t9 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "title svelte-eigrhe");
			attr(span0, "class", "numerator svelte-eigrhe");
			attr(span1, "class", "denominator svelte-eigrhe");
			attr(div0, "class", "price svelte-eigrhe");
			attr(span2, "class", "description");
			attr(header, "class", "svelte-eigrhe");
			attr(hr, "class", "svelte-eigrhe");
			attr(ul, "class", "features svelte-eigrhe");
			attr(div1, "class", "tier svelte-eigrhe");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, header);
			append_hydration(header, h3);
			append_hydration(h3, t0);
			append_hydration(header, t1);
			append_hydration(header, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, span1);
			append_hydration(span1, t4);
			append_hydration(header, t5);
			append_hydration(header, span2);
			span2.innerHTML = raw_value;
			append_hydration(div1, t6);
			append_hydration(div1, hr);
			append_hydration(div1, t7);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div1, t8);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t9);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*tiers*/ 4) && t0_value !== (t0_value = /*tier*/ ctx[3].title + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*tiers*/ 4) && t2_value !== (t2_value = /*tier*/ ctx[3].price.numerator + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*tiers*/ 4) && t4_value !== (t4_value = /*tier*/ ctx[3].price.denominator + "")) set_data(t4, t4_value);
			if ((!current || dirty & /*tiers*/ 4) && raw_value !== (raw_value = /*tier*/ ctx[3].description.html + "")) span2.innerHTML = raw_value;
			if (dirty & /*tiers*/ 4) {
				each_value_1 = /*tier*/ ctx[3].features;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$2(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*tier*/ ctx[3].link.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$6(ctx);
					if_block.c();
					if_block.m(div1, t9);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$b(ctx) {
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let div0;
	let current;
	let each_value = /*tiers*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$6(get_each_context$6(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			h3 = claim_element(section_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-eigrhe");
			attr(h3, "class", "subheading svelte-eigrhe");
			attr(div0, "class", "tiers svelte-eigrhe");
			attr(section, "class", "section-container svelte-eigrhe");
			attr(div1, "class", "section");
			attr(div1, "id", "section-2031ee1d");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, h3);
			append_hydration(h3, t2);
			append_hydration(section, t3);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (!current || dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*tiers*/ 4) {
				each_value = /*tiers*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$6(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$6(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div0, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { tiers } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('tiers' in $$props) $$invalidate(2, tiers = $$props.tiers);
	};

	return [heading, subheading, tiers];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$a, create_fragment$b, safe_not_equal, { heading: 0, subheading: 1, tiers: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$7(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i];
	return child_ctx;
}

function get_each_context_1$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].item;
	child_ctx[8] = list[i].icon;
	return child_ctx;
}

// (158:12) {#each tier.features as { item, icon }}
function create_each_block_1$3(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*item*/ ctx[7] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[8] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-1bb43vh");
			attr(span1, "class", "item svelte-1bb43vh");
			attr(li, "class", "svelte-1bb43vh");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*tiers*/ 8) icon_changes.icon = /*icon*/ ctx[8];
			icon.$set(icon_changes);
			if ((!current || dirty & /*tiers*/ 8) && t1_value !== (t1_value = /*item*/ ctx[7] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (167:10) {#if tier.link.label}
function create_if_block$7(ctx) {
	let a;
	let t_value = /*tier*/ ctx[4].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*tier*/ ctx[4].link.url);
			attr(a, "class", "button svelte-1bb43vh");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*tiers*/ 8 && t_value !== (t_value = /*tier*/ ctx[4].link.label + "")) set_data(t, t_value);

			if (dirty & /*tiers*/ 8 && a_href_value !== (a_href_value = /*tier*/ ctx[4].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (146:6) {#each tiers as tier}
function create_each_block$7(ctx) {
	let div1;
	let header;
	let div0;
	let span0;
	let t0_value = /*tier*/ ctx[4].price.numerator + "";
	let t0;
	let t1;
	let span1;
	let t2_value = /*tier*/ ctx[4].price.denominator + "";
	let t2;
	let t3;
	let h3;
	let t4_value = /*tier*/ ctx[4].title + "";
	let t4;
	let t5;
	let span2;
	let raw_value = /*tier*/ ctx[4].description.html + "";
	let t6;
	let hr;
	let t7;
	let ul;
	let t8;
	let t9;
	let current;
	let each_value_1 = /*tier*/ ctx[4].features;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$3(get_each_context_1$3(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block = /*tier*/ ctx[4].link.label && create_if_block$7(ctx);

	return {
		c() {
			div1 = element("div");
			header = element("header");
			div0 = element("div");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			h3 = element("h3");
			t4 = text(t4_value);
			t5 = space();
			span2 = element("span");
			t6 = space();
			hr = element("hr");
			t7 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			if (if_block) if_block.c();
			t9 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t4 = claim_text(h3_nodes, t4_value);
			h3_nodes.forEach(detach);
			t5 = claim_space(header_nodes);
			span2 = claim_element(header_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			span2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			hr = claim_element(div1_nodes, "HR", { class: true });
			t7 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			t9 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "numerator svelte-1bb43vh");
			attr(span1, "class", "denominator svelte-1bb43vh");
			attr(div0, "class", "price svelte-1bb43vh");
			attr(h3, "class", "title svelte-1bb43vh");
			attr(span2, "class", "description svelte-1bb43vh");
			attr(header, "class", "svelte-1bb43vh");
			attr(hr, "class", "svelte-1bb43vh");
			attr(ul, "class", "features svelte-1bb43vh");
			attr(div1, "class", "tier svelte-1bb43vh");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, header);
			append_hydration(header, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t0);
			append_hydration(div0, t1);
			append_hydration(div0, span1);
			append_hydration(span1, t2);
			append_hydration(header, t3);
			append_hydration(header, h3);
			append_hydration(h3, t4);
			append_hydration(header, t5);
			append_hydration(header, span2);
			span2.innerHTML = raw_value;
			append_hydration(div1, t6);
			append_hydration(div1, hr);
			append_hydration(div1, t7);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div1, t8);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t9);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*tiers*/ 8) && t0_value !== (t0_value = /*tier*/ ctx[4].price.numerator + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*tiers*/ 8) && t2_value !== (t2_value = /*tier*/ ctx[4].price.denominator + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*tiers*/ 8) && t4_value !== (t4_value = /*tier*/ ctx[4].title + "")) set_data(t4, t4_value);
			if ((!current || dirty & /*tiers*/ 8) && raw_value !== (raw_value = /*tier*/ ctx[4].description.html + "")) span2.innerHTML = raw_value;
			if (dirty & /*tiers*/ 8) {
				each_value_1 = /*tier*/ ctx[4].features;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$3(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*tier*/ ctx[4].link.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$7(ctx);
					if_block.c();
					if_block.m(div1, t9);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$c(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let h3;
	let t4;
	let t5;
	let div1;
	let current;
	let each_value = /*tiers*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$7(get_each_context$7(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			h3 = element("h3");
			t4 = text(/*subheading*/ ctx[2]);
			t5 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t4 = claim_text(h3_nodes, /*subheading*/ ctx[2]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead svelte-1bb43vh");
			attr(h2, "class", "heading");
			attr(h3, "class", "subheading svelte-1bb43vh");
			attr(div0, "class", "heading-group svelte-1bb43vh");
			attr(div1, "class", "tiers svelte-1bb43vh");
			attr(div2, "class", "section-container svelte-1bb43vh");
			attr(section, "class", "svelte-1bb43vh");
			attr(div3, "class", "section");
			attr(div3, "id", "section-c88bb548");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(div0, t3);
			append_hydration(div0, h3);
			append_hydration(h3, t4);
			append_hydration(div2, t5);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (!current || dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);
			if (!current || dirty & /*subheading*/ 4) set_data(t4, /*subheading*/ ctx[2]);

			if (dirty & /*tiers*/ 8) {
				each_value = /*tiers*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$7(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$7(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { tiers } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
		if ('tiers' in $$props) $$invalidate(3, tiers = $$props.tiers);
	};

	return [superhead, heading, subheading, tiers];
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$b, create_fragment$c, safe_not_equal, {
			superhead: 0,
			heading: 1,
			subheading: 2,
			tiers: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$8(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (52:4) {#each cards as card}
function create_each_block$8(ctx) {
	let div;
	let span0;
	let t0_value = /*card*/ ctx[3].stat + "";
	let t0;
	let t1;
	let span1;
	let t2_value = /*card*/ ctx[3].title + "";
	let t2;
	let t3;

	return {
		c() {
			div = element("div");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			span0 = claim_element(div_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(div_nodes);
			span1 = claim_element(div_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			t3 = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "stat svelte-l5de5u");
			attr(span1, "class", "title svelte-l5de5u");
			attr(div, "class", "card svelte-l5de5u");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, span0);
			append_hydration(span0, t0);
			append_hydration(div, t1);
			append_hydration(div, span1);
			append_hydration(span1, t2);
			append_hydration(div, t3);
		},
		p(ctx, dirty) {
			if (dirty & /*cards*/ 4 && t0_value !== (t0_value = /*card*/ ctx[3].stat + "")) set_data(t0, t0_value);
			if (dirty & /*cards*/ 4 && t2_value !== (t2_value = /*card*/ ctx[3].title + "")) set_data(t2, t2_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$d(ctx) {
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let div0;
	let each_value = /*cards*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$8(get_each_context$8(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			h3 = claim_element(section_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-l5de5u");
			attr(h3, "class", "subheading svelte-l5de5u");
			attr(div0, "class", "cards svelte-l5de5u");
			attr(section, "class", "section-container svelte-l5de5u");
			attr(div1, "class", "section");
			attr(div1, "id", "section-62f19f08");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, h3);
			append_hydration(h3, t2);
			append_hydration(section, t3);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*cards*/ 4) {
				each_value = /*cards*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$8(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$8(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$c($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('cards' in $$props) $$invalidate(2, cards = $$props.cards);
	};

	return [heading, subheading, cards];
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$c, create_fragment$d, safe_not_equal, { heading: 0, subheading: 1, cards: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$9(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	child_ctx[5] = i;
	return child_ctx;
}

// (55:2) {#if buttons.length > 0}
function create_if_block$8(ctx) {
	let div;
	let each_value = /*buttons*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$9(get_each_context$9(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "buttons svelte-1tp7z49");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}
		},
		p(ctx, dirty) {
			if (dirty & /*buttons*/ 4) {
				each_value = /*buttons*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$9(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$9(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

// (57:6) {#each buttons as button, i}
function create_each_block$9(ctx) {
	let a;
	let t_value = /*button*/ ctx[3].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-1tp7z49");
			attr(a, "href", a_href_value = /*button*/ ctx[3].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*buttons*/ 4 && t_value !== (t_value = /*button*/ ctx[3].link.label + "")) set_data(t, t_value);

			if (dirty & /*buttons*/ 4 && a_href_value !== (a_href_value = /*button*/ ctx[3].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$e(ctx) {
	let div;
	let header;
	let h1;
	let t0;
	let t1;
	let span;
	let t2;
	let t3;
	let if_block = /*buttons*/ ctx[2].length > 0 && create_if_block$8(ctx);

	return {
		c() {
			div = element("div");
			header = element("header");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			span = element("span");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			header = claim_element(div_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h1 = claim_element(header_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, /*subheading*/ ctx[1]);
			span_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			if (if_block) if_block.l(header_nodes);
			header_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "heading svelte-1tp7z49");
			attr(span, "class", "subheading svelte-1tp7z49");
			attr(header, "class", "section-container svelte-1tp7z49");
			attr(div, "class", "section");
			attr(div, "id", "section-67ead2dd");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, header);
			append_hydration(header, h1);
			append_hydration(h1, t0);
			append_hydration(header, t1);
			append_hydration(header, span);
			append_hydration(span, t2);
			append_hydration(header, t3);
			if (if_block) if_block.m(header, null);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (/*buttons*/ ctx[2].length > 0) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$8(ctx);
					if_block.c();
					if_block.m(header, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			if (if_block) if_block.d();
		}
	};
}

function instance$d($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { buttons } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('buttons' in $$props) $$invalidate(2, buttons = $$props.buttons);
	};

	return [heading, subheading, buttons];
}

class Component$e extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$d, create_fragment$e, safe_not_equal, { heading: 0, subheading: 1, buttons: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$f(ctx) {
	let div1;
	let section;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;
	let div0;
	let raw_value = /*content*/ ctx[1].html + "";

	return {
		c() {
			div1 = element("div");
			section = element("section");
			img = element("img");
			t = space();
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			img = claim_element(section_nodes, "IMG", { src: true, alt: true });
			t = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			attr(div0, "class", "content svelte-g4ok1j");
			attr(section, "class", "section-container svelte-g4ok1j");
			attr(div1, "class", "section");
			attr(div1, "id", "section-ec11f906");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, img);
			append_hydration(section, t);
			append_hydration(section, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content*/ 2 && raw_value !== (raw_value = /*content*/ ctx[1].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$e($$self, $$props, $$invalidate) {
	let { image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
		if ('content' in $$props) $$invalidate(1, content = $$props.content);
	};

	return [image, content];
}

class Component$f extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$e, create_fragment$f, safe_not_equal, { image: 0, content: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$a(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (50:6) {#each buttons as button}
function create_each_block$a(ctx) {
	let a;
	let icon;
	let t0;
	let span;
	let t1_value = /*button*/ ctx[3].link.label + "";
	let t1;
	let t2;
	let a_href_value;
	let current;
	icon = new Component$3({ props: { icon: /*button*/ ctx[3].icon } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t0 = space();
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t0 = claim_space(a_nodes);
			span = claim_element(a_nodes, "SPAN", {});
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-o9z257");
			attr(a, "href", a_href_value = /*button*/ ctx[3].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t0);
			append_hydration(a, span);
			append_hydration(span, t1);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*buttons*/ 4) icon_changes.icon = /*button*/ ctx[3].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*buttons*/ 4) && t1_value !== (t1_value = /*button*/ ctx[3].link.label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*buttons*/ 4 && a_href_value !== (a_href_value = /*button*/ ctx[3].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$g(ctx) {
	let div3;
	let section;
	let div2;
	let h2;
	let t0;
	let t1;
	let div0;
	let raw_value = /*body*/ ctx[1].html + "";
	let t2;
	let div1;
	let current;
	let each_value = /*buttons*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$a(get_each_context$a(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h2 = claim_element(div2_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-o9z257");
			attr(div0, "class", "body svelte-o9z257");
			attr(div1, "class", "buttons svelte-o9z257");
			attr(div2, "class", "card svelte-o9z257");
			attr(section, "class", "section-container svelte-o9z257");
			attr(div3, "class", "section");
			attr(div3, "id", "section-6458d1ef");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, h2);
			append_hydration(h2, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t2);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if ((!current || dirty & /*body*/ 2) && raw_value !== (raw_value = /*body*/ ctx[1].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*buttons*/ 4) {
				each_value = /*buttons*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$a(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$a(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$f($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { body } = $$props;
	let { buttons } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('body' in $$props) $$invalidate(1, body = $$props.body);
		if ('buttons' in $$props) $$invalidate(2, buttons = $$props.buttons);
	};

	return [heading, body, buttons];
}

class Component$g extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$f, create_fragment$g, safe_not_equal, { heading: 0, body: 1, buttons: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$b(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	child_ctx[4] = list[i].icon;
	return child_ctx;
}

// (76:4) {#if email}
function create_if_block$9(ctx) {
	let a;
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(/*email*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, /*email*/ ctx[1]);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-fjx86h");
			attr(a, "href", a_href_value = "mailto:" + /*email*/ ctx[1]);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*email*/ 2) set_data(t, /*email*/ ctx[1]);

			if (dirty & /*email*/ 2 && a_href_value !== (a_href_value = "mailto:" + /*email*/ ctx[1])) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (80:6) {#each social as {link, icon}}
function create_each_block$b(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[3].label);
			attr(a, "class", "svelte-fjx86h");
			attr(li, "class", "svelte-fjx86h");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 4) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 4 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[3].label)) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$h(ctx) {
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let t2;
	let ul;
	let current;
	let if_block = /*email*/ ctx[1] && create_if_block$9(ctx);
	let each_value = /*social*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$b(get_each_context$b(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			if (if_block) if_block.l(div0_nodes);
			t2 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-fjx86h");
			attr(ul, "class", "svelte-fjx86h");
			attr(div0, "class", "card svelte-fjx86h");
			attr(section, "class", "section-container svelte-fjx86h");
			attr(div1, "class", "section");
			attr(div1, "id", "section-4bbab409");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			if (if_block) if_block.m(div0, null);
			append_hydration(div0, t2);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (/*email*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$9(ctx);
					if_block.c();
					if_block.m(div0, t2);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*social*/ 4) {
				each_value = /*social*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$b(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$b(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$g($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { email } = $$props;
	let { social } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('email' in $$props) $$invalidate(1, email = $$props.email);
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
	};

	return [heading, email, social];
}

class Component$h extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$g, create_fragment$h, safe_not_equal, { heading: 0, email: 1, social: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$c(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	child_ctx[5] = i;
	return child_ctx;
}

// (69:4) {#each cards as card, i}
function create_each_block$c(ctx) {
	let li;
	let span0;
	let t0_value = /*i*/ ctx[5] + 1 + "";
	let t0;
	let t1;
	let t2;
	let div;
	let span1;
	let t3_value = /*card*/ ctx[3].title + "";
	let t3;
	let t4;
	let span2;
	let raw_value = /*card*/ ctx[3].subtitle.html + "";
	let t5;

	return {
		c() {
			li = element("li");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = text(".");
			t2 = space();
			div = element("div");
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			span2 = element("span");
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			t1 = claim_text(span0_nodes, ".");
			span0_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			div = claim_element(li_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			span1 = claim_element(div_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			t4 = claim_space(div_nodes);
			span2 = claim_element(div_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			span2_nodes.forEach(detach);
			div_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "number svelte-1uh5akc");
			attr(span1, "class", "title svelte-1uh5akc");
			attr(span2, "class", "subtitle");
			attr(div, "class", "body svelte-1uh5akc");
			attr(li, "class", "svelte-1uh5akc");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			append_hydration(span0, t0);
			append_hydration(span0, t1);
			append_hydration(li, t2);
			append_hydration(li, div);
			append_hydration(div, span1);
			append_hydration(span1, t3);
			append_hydration(div, t4);
			append_hydration(div, span2);
			span2.innerHTML = raw_value;
			append_hydration(li, t5);
		},
		p(ctx, dirty) {
			if (dirty & /*cards*/ 2 && t3_value !== (t3_value = /*card*/ ctx[3].title + "")) set_data(t3, t3_value);
			if (dirty & /*cards*/ 2 && raw_value !== (raw_value = /*card*/ ctx[3].subtitle.html + "")) span2.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (79:2) {#if button.link.label}
function create_if_block$a(ctx) {
	let a;
	let t_value = /*button*/ ctx[2].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-1uh5akc");
			attr(a, "href", a_href_value = /*button*/ ctx[2].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*button*/ 4 && t_value !== (t_value = /*button*/ ctx[2].link.label + "")) set_data(t, t_value);

			if (dirty & /*button*/ 4 && a_href_value !== (a_href_value = /*button*/ ctx[2].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$i(ctx) {
	let div;
	let section;
	let h2;
	let t0;
	let t1;
	let ol;
	let t2;
	let each_value = /*cards*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$c(get_each_context$c(ctx, each_value, i));
	}

	let if_block = /*button*/ ctx[2].link.label && create_if_block$a(ctx);

	return {
		c() {
			div = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ol = element("ol");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ol = claim_element(section_nodes, "OL", { class: true });
			var ol_nodes = children(ol);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ol_nodes);
			}

			ol_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			if (if_block) if_block.l(section_nodes);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1uh5akc");
			attr(ol, "class", "svelte-1uh5akc");
			attr(section, "class", "section-container svelte-1uh5akc");
			attr(div, "class", "section");
			attr(div, "id", "section-09221e3f");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ol);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ol, null);
				}
			}

			append_hydration(section, t2);
			if (if_block) if_block.m(section, null);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*cards*/ 2) {
				each_value = /*cards*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$c(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$c(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ol, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (/*button*/ ctx[2].link.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$a(ctx);
					if_block.c();
					if_block.m(section, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

function instance$h($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { cards } = $$props;
	let { button } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('cards' in $$props) $$invalidate(1, cards = $$props.cards);
		if ('button' in $$props) $$invalidate(2, button = $$props.button);
	};

	return [heading, cards, button];
}

class Component$i extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$h, create_fragment$i, safe_not_equal, { heading: 0, cards: 1, button: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$d(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i].link;
	return child_ctx;
}

// (26:4) {#each footer_links as { link }}
function create_each_block$d(ctx) {
	let a;
	let t_value = /*link*/ ctx[1].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link");
			attr(a, "href", a_href_value = /*link*/ ctx[1].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 1 && t_value !== (t_value = /*link*/ ctx[1].label + "")) set_data(t, t_value);

			if (dirty & /*footer_links*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$j(ctx) {
	let div;
	let footer;
	let nav;
	let t0;
	let span;
	let t1;
	let a;
	let t2;
	let each_value = /*footer_links*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$d(get_each_context$d(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");
			footer = element("footer");
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			t1 = text("Powered by\n    ");
			a = element("a");
			t2 = text("Primo");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			footer = claim_element(div_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav = claim_element(footer_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, "Powered by\n    ");
			a = claim_element(span_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, "Primo");
			a_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-1x6qn6a");
			attr(a, "href", "https://primo.so");
			attr(a, "class", "primo svelte-1x6qn6a");
			attr(span, "class", "primo svelte-1x6qn6a");
			attr(footer, "class", "section-container svelte-1x6qn6a");
			attr(div, "class", "section");
			attr(div, "id", "section-68f15efd");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, footer);
			append_hydration(footer, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, t1);
			append_hydration(span, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*footer_links*/ 1) {
				each_value = /*footer_links*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$d(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$d(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$i($$self, $$props, $$invalidate) {
	let { footer_links } = $$props;

	$$self.$$set = $$props => {
		if ('footer_links' in $$props) $$invalidate(0, footer_links = $$props.footer_links);
	};

	return [footer_links];
}

class Component$j extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$i, create_fragment$j, safe_not_equal, { footer_links: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$e(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (43:4) {#each items as item}
function create_each_block$e(ctx) {
	let div1;
	let h2;
	let t0_value = /*item*/ ctx[3].title + "";
	let t0;
	let t1;
	let div0;
	let raw_value = /*item*/ ctx[3].description.html + "";
	let t2;

	return {
		c() {
			div1 = element("div");
			h2 = element("h2");
			t0 = text(t0_value);
			t1 = space();
			div0 = element("div");
			t2 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, t0_value);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title svelte-ghakxq");
			attr(div0, "class", "description");
			attr(div1, "class", "item svelte-ghakxq");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && t0_value !== (t0_value = /*item*/ ctx[3].title + "")) set_data(t0, t0_value);
			if (dirty & /*items*/ 2 && raw_value !== (raw_value = /*item*/ ctx[3].description.html + "")) div0.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function create_fragment$k(ctx) {
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let div0;
	let section_class_value;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$e(get_each_context$e(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-ghakxq");
			attr(div0, "class", "items svelte-ghakxq");
			attr(section, "class", section_class_value = "section-container " + /*variation*/ ctx[2] + " svelte-ghakxq");
			attr(div1, "class", "section");
			attr(div1, "id", "section-95ff502d");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$e(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$e(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*variation*/ 4 && section_class_value !== (section_class_value = "section-container " + /*variation*/ ctx[2] + " svelte-ghakxq")) {
				attr(section, "class", section_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$j($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { items } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
		if ('variation' in $$props) $$invalidate(2, variation = $$props.variation);
	};

	return [heading, items, variation];
}

class Component$k extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$j, create_fragment$k, safe_not_equal, { heading: 0, items: 1, variation: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$f(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].image;
	return child_ctx;
}

// (32:6) {#each items as {image}}
function create_each_block$f(ctx) {
	let div;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;

	return {
		c() {
			div = element("div");
			img = element("img");
			t = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			img = claim_element(div_nodes, "IMG", { src: true, alt: true });
			t = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(div, "class", "item svelte-1s5lign");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, img);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$l(ctx) {
	let div2;
	let section;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$f(get_each_context$f(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", {});
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1s5lign");
			attr(div0, "class", "items svelte-1s5lign");
			attr(div1, "class", "section-container");
			attr(div2, "class", "section");
			attr(div2, "id", "section-8132d1a2");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$f(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$f(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$k($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items];
}

class Component$l extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$k, create_fragment$l, safe_not_equal, { heading: 0, items: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$m(ctx) {
	let div;
	let section;
	let h1;
	let t;

	return {
		c() {
			div = element("div");
			section = element("section");
			h1 = element("h1");
			t = text(/*headline*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h1 = claim_element(section_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t = claim_text(h1_nodes, /*headline*/ ctx[0]);
			h1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-1au42aa");
			attr(section, "class", "section-container svelte-1au42aa");
			attr(div, "class", "section");
			attr(div, "id", "section-fcc8373d");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, h1);
			append_hydration(h1, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*headline*/ 1) set_data(t, /*headline*/ ctx[0]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$l($$self, $$props, $$invalidate) {
	let { headline } = $$props;

	$$self.$$set = $$props => {
		if ('headline' in $$props) $$invalidate(0, headline = $$props.headline);
	};

	return [headline];
}

class Component$m extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$l, create_fragment$m, safe_not_equal, { headline: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$g(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	child_ctx[7] = i;
	return child_ctx;
}

// (80:6) {#if activeItem === i}
function create_if_block$b(ctx) {
	let div;
	let raw_value = /*item*/ ctx[5].description.html + "";
	let div_transition;
	let current;

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "description svelte-1oe3rov");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			div.innerHTML = raw_value;
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*items*/ 2) && raw_value !== (raw_value = /*item*/ ctx[5].description.html + "")) div.innerHTML = raw_value;		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!current) return;
				if (!div_transition) div_transition = create_bidirectional_transition(div, slide, {}, true);
				div_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!div_transition) div_transition = create_bidirectional_transition(div, slide, {}, false);
			div_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (detaching && div_transition) div_transition.end();
		}
	};
}

// (72:4) {#each items as item, i (i)}
function create_each_block$g(key_1, ctx) {
	let div1;
	let button;
	let span0;
	let t0_value = /*item*/ ctx[5].title + "";
	let t0;
	let t1;
	let span1;
	let icon;
	let t2;
	let t3;
	let t4;
	let current;
	let mounted;
	let dispose;
	icon = new Component$3({ props: { icon: "ph:caret-down-bold" } });

	function click_handler() {
		return /*click_handler*/ ctx[4](/*i*/ ctx[7]);
	}

	let if_block = /*activeItem*/ ctx[2] === /*i*/ ctx[7] && create_if_block$b(ctx);

	return {
		key: key_1,
		first: null,
		c() {
			div1 = element("div");
			button = element("button");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			create_component(icon.$$.fragment);
			t2 = space();
			if (if_block) if_block.c();
			t3 = space();
			t4 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			button = claim_element(div1_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			span0 = claim_element(button_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(button_nodes);
			span1 = claim_element(button_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			claim_component(icon.$$.fragment, span1_nodes);
			span1_nodes.forEach(detach);
			button_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			t3 = claim_space(div1_nodes);
			t4 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-1oe3rov");
			attr(span1, "class", "icon svelte-1oe3rov");
			attr(button, "class", "svelte-1oe3rov");
			attr(div1, "class", "item svelte-1oe3rov");
			toggle_class(div1, "active", /*activeItem*/ ctx[2] === /*i*/ ctx[7]);
			this.first = div1;
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, button);
			append_hydration(button, span0);
			append_hydration(span0, t0);
			append_hydration(button, t1);
			append_hydration(button, span1);
			mount_component(icon, span1, null);
			append_hydration(div1, t2);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t3);
			append_hydration(div1, t4);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", click_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if ((!current || dirty & /*items*/ 2) && t0_value !== (t0_value = /*item*/ ctx[5].title + "")) set_data(t0, t0_value);

			if (/*activeItem*/ ctx[2] === /*i*/ ctx[7]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*activeItem, items*/ 6) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$b(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div1, t3);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}

			if (!current || dirty & /*activeItem, items*/ 6) {
				toggle_class(div1, "active", /*activeItem*/ ctx[2] === /*i*/ ctx[7]);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_component(icon);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$n(ctx) {
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let div0;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let current;
	let each_value = /*items*/ ctx[1];
	const get_key = ctx => /*i*/ ctx[7];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$g(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$g(key, child_ctx));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1oe3rov");
			attr(div0, "class", "accordion svelte-1oe3rov");
			attr(section, "class", "section-container svelte-1oe3rov");
			attr(div1, "class", "section");
			attr(div1, "id", "section-0ec867e3");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*activeItem, items, setActiveItem*/ 14) {
				each_value = /*items*/ ctx[1];
				group_outros();
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, div0, outro_and_destroy_block, create_each_block$g, null, get_each_context$g);
				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}
		}
	};
}

function instance$m($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { items } = $$props;
	let activeItem = 0;

	function setActiveItem(i) {
		$$invalidate(2, activeItem = activeItem === i ? null : i);
	}

	const click_handler = i => setActiveItem(i);

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items, activeItem, setActiveItem, click_handler];
}

class Component$n extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$m, create_fragment$n, safe_not_equal, { heading: 0, items: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$h(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_1$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (125:33) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[2].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[2].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 4 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[2].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 4 && img_alt_value !== (img_alt_value = /*logo*/ ctx[2].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (123:8) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[2].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 4 && t_value !== (t_value = /*logo*/ ctx[2].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (130:8) {#each site_nav as { link }}
function create_each_block_1$4(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-19bt6nw");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			toggle_class(a, "active", /*link*/ ctx[8].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 8 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 8 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 8) {
				toggle_class(a, "active", /*link*/ ctx[8].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (139:33) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[2].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[2].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 4 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[2].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 4 && img_alt_value !== (img_alt_value = /*logo*/ ctx[2].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (137:8) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[2].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 4 && t_value !== (t_value = /*logo*/ ctx[2].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (149:6) {#if mobileNavOpen}
function create_if_block$c(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$h(get_each_context$h(ctx, each_value, i));
	}

	icon = new Component$3({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-19bt6nw");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-19bt6nw");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 8) {
				each_value = /*site_nav*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$h(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$h(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (151:10) {#each site_nav as { link }}
function create_each_block$h(ctx) {
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 8 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 8 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$o(ctx) {
	let div4;
	let header;
	let div2;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let div1;
	let a1;
	let t2;
	let button;
	let icon;
	let t3;
	let t4;
	let div3;
	let h1;
	let t5;
	let header_aria_label_value;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[2].title) return create_if_block_3;
		if (/*logo*/ ctx[2].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$4(get_each_context_1$4(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[2].title) return create_if_block_1$1;
		if (/*logo*/ ctx[2].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$3({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[4] && create_if_block$c(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div2 = element("div");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block2) if_block2.c();
			t4 = space();
			div3 = element("div");
			h1 = element("h1");
			t5 = text(/*headline*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);

			header = claim_element(div4_nodes, "HEADER", {
				style: true,
				role: true,
				"aria-label": true,
				class: true
			});

			var header_nodes = children(header);
			div2 = claim_element(header_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			a1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t4 = claim_space(header_nodes);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h1 = claim_element(div3_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t5 = claim_text(h1_nodes, /*headline*/ ctx[1]);
			h1_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-19bt6nw");
			attr(nav, "class", "svelte-19bt6nw");
			attr(div0, "class", "desktop-nav svelte-19bt6nw");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-19bt6nw");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-19bt6nw");
			attr(div2, "class", "section-container svelte-19bt6nw");
			attr(h1, "class", "headline svelte-19bt6nw");
			attr(div3, "class", "section-container svelte-19bt6nw");
			set_style(header, "background-image", "url('" + /*background*/ ctx[0].url + "')");
			attr(header, "role", "img");
			attr(header, "aria-label", header_aria_label_value = /*background*/ ctx[0].alt);
			attr(header, "class", "svelte-19bt6nw");
			attr(div4, "class", "section");
			attr(div4, "id", "section-46f0cce2");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(div1, t2);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block2) if_block2.m(div1, null);
			append_hydration(header, t4);
			append_hydration(header, div3);
			append_hydration(div3, h1);
			append_hydration(h1, t5);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav, window*/ 8) {
				each_value_1 = /*site_nav*/ ctx[3];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$4(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$4(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a1, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[4]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 16) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$c(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}

			if (!current || dirty & /*headline*/ 2) set_data(t5, /*headline*/ ctx[1]);

			if (!current || dirty & /*background*/ 1) {
				set_style(header, "background-image", "url('" + /*background*/ ctx[0].url + "')");
			}

			if (!current || dirty & /*background*/ 1 && header_aria_label_value !== (header_aria_label_value = /*background*/ ctx[0].alt)) {
				attr(header, "aria-label", header_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$n($$self, $$props, $$invalidate) {
	let { background } = $$props;
	let { headline } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(4, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(4, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('background' in $$props) $$invalidate(0, background = $$props.background);
		if ('headline' in $$props) $$invalidate(1, headline = $$props.headline);
		if ('logo' in $$props) $$invalidate(2, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(3, site_nav = $$props.site_nav);
	};

	return [
		background,
		headline,
		logo,
		site_nav,
		mobileNavOpen,
		click_handler,
		click_handler_1
	];
}

class Component$o extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$n, create_fragment$o, safe_not_equal, {
			background: 0,
			headline: 1,
			logo: 2,
			site_nav: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$i(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i];
	return child_ctx;
}

// (80:8) {#if teaser.image.url}
function create_if_block_1$2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*teaser*/ ctx[1].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*teaser*/ ctx[1].image.alt);
			attr(img, "class", "svelte-1re4jxk");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 1 && !src_url_equal(img.src, img_src_value = /*teaser*/ ctx[1].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*teasers*/ 1 && img_alt_value !== (img_alt_value = /*teaser*/ ctx[1].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (86:10) {#if teaser.link.url}
function create_if_block$d(ctx) {
	let a;
	let t_value = /*teaser*/ ctx[1].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-1re4jxk");
			attr(a, "href", a_href_value = /*teaser*/ ctx[1].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 1 && t_value !== (t_value = /*teaser*/ ctx[1].link.label + "")) set_data(t, t_value);

			if (dirty & /*teasers*/ 1 && a_href_value !== (a_href_value = /*teaser*/ ctx[1].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (78:4) {#each teasers as teaser}
function create_each_block$i(ctx) {
	let div2;
	let t0;
	let div1;
	let h2;
	let t1_value = /*teaser*/ ctx[1].title + "";
	let t1;
	let t2;
	let div0;
	let raw_value = /*teaser*/ ctx[1].content.html + "";
	let t3;
	let t4;
	let if_block0 = /*teaser*/ ctx[1].image.url && create_if_block_1$2(ctx);
	let if_block1 = /*teaser*/ ctx[1].link.url && create_if_block$d(ctx);

	return {
		c() {
			div2 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			div1 = element("div");
			h2 = element("h2");
			t1 = text(t1_value);
			t2 = space();
			div0 = element("div");
			t3 = space();
			if (if_block1) if_block1.c();
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block0) if_block0.l(div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, t1_value);
			h2_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title svelte-1re4jxk");
			attr(div0, "class", "content");
			attr(div1, "class", "body svelte-1re4jxk");
			attr(div2, "class", "teaser svelte-1re4jxk");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			if (if_block0) if_block0.m(div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t3);
			if (if_block1) if_block1.m(div1, null);
			append_hydration(div2, t4);
		},
		p(ctx, dirty) {
			if (/*teaser*/ ctx[1].image.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_1$2(ctx);
					if_block0.c();
					if_block0.m(div2, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (dirty & /*teasers*/ 1 && t1_value !== (t1_value = /*teaser*/ ctx[1].title + "")) set_data(t1, t1_value);
			if (dirty & /*teasers*/ 1 && raw_value !== (raw_value = /*teaser*/ ctx[1].content.html + "")) div0.innerHTML = raw_value;
			if (/*teaser*/ ctx[1].link.url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block$d(ctx);
					if_block1.c();
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function create_fragment$p(ctx) {
	let div1;
	let section;
	let div0;
	let each_value = /*teasers*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$i(get_each_context$i(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "teasers svelte-1re4jxk");
			attr(section, "class", "section-container");
			attr(div1, "class", "section");
			attr(div1, "id", "section-5eb60823");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*teasers*/ 1) {
				each_value = /*teasers*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$i(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$i(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$o($$self, $$props, $$invalidate) {
	let { teasers } = $$props;

	$$self.$$set = $$props => {
		if ('teasers' in $$props) $$invalidate(0, teasers = $$props.teasers);
	};

	return [teasers];
}

class Component$p extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$o, create_fragment$p, safe_not_equal, { teasers: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$q(ctx) {
	let div1;
	let section;
	let header;
	let h2;
	let t0;
	let t1;
	let a;
	let t2_value = /*link*/ ctx[1].label + "";
	let t2;
	let a_href_value;
	let t3;
	let div0;
	let raw_value = /*content*/ ctx[2].html + "";

	return {
		c() {
			div1 = element("div");
			section = element("section");
			header = element("header");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			a = element("a");
			t2 = text(t2_value);
			t3 = space();
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			a = claim_element(header_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-qz2vy1");
			attr(a, "href", a_href_value = /*link*/ ctx[1].url);
			attr(a, "class", "button");
			attr(header, "class", "svelte-qz2vy1");
			attr(div0, "class", "content svelte-qz2vy1");
			attr(section, "class", "section-container svelte-qz2vy1");
			attr(div1, "class", "section");
			attr(div1, "id", "section-d70004b4");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, header);
			append_hydration(header, h2);
			append_hydration(h2, t0);
			append_hydration(header, t1);
			append_hydration(header, a);
			append_hydration(a, t2);
			append_hydration(section, t3);
			append_hydration(section, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*link*/ 2 && t2_value !== (t2_value = /*link*/ ctx[1].label + "")) set_data(t2, t2_value);

			if (dirty & /*link*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*content*/ 4 && raw_value !== (raw_value = /*content*/ ctx[2].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$p($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { link } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('link' in $$props) $$invalidate(1, link = $$props.link);
		if ('content' in $$props) $$invalidate(2, content = $$props.content);
	};

	return [heading, link, content];
}

class Component$q extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$p, create_fragment$q, safe_not_equal, { heading: 0, link: 1, content: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$j(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i];
	return child_ctx;
}

function get_each_context_1$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].link;
	child_ctx[6] = list[i].icon;
	return child_ctx;
}

// (89:6) {#if person.image.url}
function create_if_block$e(ctx) {
	let figure;
	let img;
	let img_alt_value;
	let img_src_value;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { alt: true, src: true, class: true });
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "alt", img_alt_value = /*person*/ ctx[2].image.alt);
			if (!src_url_equal(img.src, img_src_value = /*person*/ ctx[2].image.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-is93z9");
			attr(figure, "class", "svelte-is93z9");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
		},
		p(ctx, dirty) {
			if (dirty & /*people*/ 2 && img_alt_value !== (img_alt_value = /*person*/ ctx[2].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*people*/ 2 && !src_url_equal(img.src, img_src_value = /*person*/ ctx[2].image.url)) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(figure);
		}
	};
}

// (100:10) {#each person.social_links as {link, icon}}
function create_each_block_1$5(ctx) {
	let a;
	let icon;
	let t;
	let a_href_value;
	let a_aria_label_value;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[6] } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[5].url);
			attr(a, "aria-label", a_aria_label_value = /*link*/ ctx[5].label);
			attr(a, "class", "svelte-is93z9");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*people*/ 2) icon_changes.icon = /*icon*/ ctx[6];
			icon.$set(icon_changes);

			if (!current || dirty & /*people*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[5].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*people*/ 2 && a_aria_label_value !== (a_aria_label_value = /*link*/ ctx[5].label)) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (87:4) {#each people as person}
function create_each_block$j(ctx) {
	let li;
	let t0;
	let div2;
	let div0;
	let span0;
	let t1_value = /*person*/ ctx[2].name + "";
	let t1;
	let t2;
	let span1;
	let t3_value = /*person*/ ctx[2].title + "";
	let t3;
	let t4;
	let div1;
	let t5;
	let current;
	let if_block = /*person*/ ctx[2].image.url && create_if_block$e(ctx);
	let each_value_1 = /*person*/ ctx[2].social_links;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$5(get_each_context_1$5(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			li = element("li");
			if (if_block) if_block.c();
			t0 = space();
			div2 = element("div");
			div0 = element("div");
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			if (if_block) if_block.l(li_nodes);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "name svelte-is93z9");
			attr(span1, "class", "title svelte-is93z9");
			attr(div0, "class", "details svelte-is93z9");
			attr(div1, "class", "social svelte-is93z9");
			attr(div2, "class", "info");
			attr(li, "class", "svelte-is93z9");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, span1);
			append_hydration(span1, t3);
			append_hydration(div2, t4);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(li, t5);
			current = true;
		},
		p(ctx, dirty) {
			if (/*person*/ ctx[2].image.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$e(ctx);
					if_block.c();
					if_block.m(li, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if ((!current || dirty & /*people*/ 2) && t1_value !== (t1_value = /*person*/ ctx[2].name + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*people*/ 2) && t3_value !== (t3_value = /*person*/ ctx[2].title + "")) set_data(t3, t3_value);

			if (dirty & /*people*/ 2) {
				each_value_1 = /*person*/ ctx[2].social_links;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$5(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1$5(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$r(ctx) {
	let div;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let current;
	let each_value = /*people*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$j(get_each_context$j(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-is93z9");
			attr(ul, "class", "cards svelte-is93z9");
			attr(section, "class", "section-container svelte-is93z9");
			attr(div, "class", "section");
			attr(div, "id", "section-897d417e");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*people*/ 2) {
				each_value = /*people*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$j(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$j(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$q($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { people } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('people' in $$props) $$invalidate(1, people = $$props.people);
	};

	return [heading, people];
}

class Component$r extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$q, create_fragment$r, safe_not_equal, { heading: 0, people: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$k(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i].title;
	child_ctx[2] = list[i].link;
	return child_ctx;
}

// (30:4) {#each items as { title, link }}
function create_each_block$k(ctx) {
	let div;
	let span;
	let t0_value = /*title*/ ctx[1] + "";
	let t0;
	let t1;
	let a;
	let t2_value = /*link*/ ctx[2].label + "";
	let t2;
	let a_href_value;
	let t3;

	return {
		c() {
			div = element("div");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			a = element("a");
			t2 = text(t2_value);
			t3 = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			span = claim_element(div_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(div_nodes);
			a = claim_element(div_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			t3 = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "title svelte-19cnxo1");
			attr(a, "href", a_href_value = /*link*/ ctx[2].url);
			attr(a, "class", "link svelte-19cnxo1");
			attr(div, "class", "item svelte-19cnxo1");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, span);
			append_hydration(span, t0);
			append_hydration(div, t1);
			append_hydration(div, a);
			append_hydration(a, t2);
			append_hydration(div, t3);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && t0_value !== (t0_value = /*title*/ ctx[1] + "")) set_data(t0, t0_value);
			if (dirty & /*items*/ 1 && t2_value !== (t2_value = /*link*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (dirty & /*items*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$s(ctx) {
	let div2;
	let div1;
	let div0;
	let each_value = /*items*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$k(get_each_context$k(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "items svelte-19cnxo1");
			attr(div1, "class", "section-container");
			attr(div2, "class", "section");
			attr(div2, "id", "section-980e7634");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*items*/ 1) {
				each_value = /*items*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$k(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$k(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$r($$self, $$props, $$invalidate) {
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('items' in $$props) $$invalidate(0, items = $$props.items);
	};

	return [items];
}

class Component$s extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$r, create_fragment$s, safe_not_equal, { items: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$l(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i];
	return child_ctx;
}

// (48:8) {#if item.image.url}
function create_if_block$f(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[1].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*item*/ ctx[1].image.alt);
			attr(img, "class", "svelte-dg30bs");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[1].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 1 && img_alt_value !== (img_alt_value = /*item*/ ctx[1].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (46:4) {#each items as item}
function create_each_block$l(ctx) {
	let div2;
	let t0;
	let div1;
	let h2;
	let t1_value = /*item*/ ctx[1].title + "";
	let t1;
	let t2;
	let div0;
	let raw_value = /*item*/ ctx[1].description + "";
	let t3;
	let if_block = /*item*/ ctx[1].image.url && create_if_block$f(ctx);

	return {
		c() {
			div2 = element("div");
			if (if_block) if_block.c();
			t0 = space();
			div1 = element("div");
			h2 = element("h2");
			t1 = text(t1_value);
			t2 = space();
			div0 = element("div");
			t3 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block) if_block.l(div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, t1_value);
			h2_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title heading svelte-dg30bs");
			attr(div0, "class", "description");
			attr(div1, "class", "body svelte-dg30bs");
			attr(div2, "class", "item svelte-dg30bs");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			if (if_block) if_block.m(div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t3);
		},
		p(ctx, dirty) {
			if (/*item*/ ctx[1].image.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$f(ctx);
					if_block.c();
					if_block.m(div2, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*items*/ 1 && t1_value !== (t1_value = /*item*/ ctx[1].title + "")) set_data(t1, t1_value);
			if (dirty & /*items*/ 1 && raw_value !== (raw_value = /*item*/ ctx[1].description + "")) div0.innerHTML = raw_value;		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$t(ctx) {
	let div1;
	let section;
	let div0;
	let each_value = /*items*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$l(get_each_context$l(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "items svelte-dg30bs");
			attr(section, "class", "section-container svelte-dg30bs");
			attr(div1, "class", "section");
			attr(div1, "id", "section-875a048c");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*items*/ 1) {
				each_value = /*items*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$l(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$l(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$s($$self, $$props, $$invalidate) {
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('items' in $$props) $$invalidate(0, items = $$props.items);
	};

	return [items];
}

class Component$t extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$s, create_fragment$t, safe_not_equal, { items: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$u(ctx) {
	let div1;
	let div0;
	let feature;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			feature = element("feature");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			feature = claim_element(div0_nodes, "FEATURE", {});
			var feature_nodes = children(feature);
			img = claim_element(feature_nodes, "IMG", { class: true, src: true, alt: true });
			feature_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "class", "image svelte-12mvx2f");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			attr(div0, "class", "section-container svelte-12mvx2f");
			attr(div1, "class", "section");
			attr(div1, "id", "section-0166be11");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, feature);
			append_hydration(feature, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$t($$self, $$props, $$invalidate) {
	let { image } = $$props;

	$$self.$$set = $$props => {
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
	};

	return [image];
}

class Component$u extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$t, create_fragment$u, safe_not_equal, { image: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$v(ctx) {
	let div;
	let header;
	let span;
	let t0;
	let t1;
	let h1;
	let t2;
	let t3;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div = element("div");
			header = element("header");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h1 = element("h1");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			img = element("img");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			header = claim_element(div_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h1 = claim_element(header_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t2 = claim_text(h1_nodes, /*heading*/ ctx[1]);
			h1_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			img = claim_element(header_nodes, "IMG", { src: true, alt: true, class: true });
			header_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead svelte-p3sbrw");
			attr(h1, "class", "heading svelte-p3sbrw");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(img, "class", "svelte-p3sbrw");
			attr(header, "class", "section-container svelte-p3sbrw");
			attr(div, "class", "section");
			attr(div, "id", "section-45716e99");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, header);
			append_hydration(header, span);
			append_hydration(span, t0);
			append_hydration(header, t1);
			append_hydration(header, h1);
			append_hydration(h1, t2);
			append_hydration(header, t3);
			append_hydration(header, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);

			if (dirty & /*image*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$u($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { image } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
	};

	return [superhead, heading, image];
}

class Component$v extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$u, create_fragment$v, safe_not_equal, { superhead: 0, heading: 1, image: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$m(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].icon;
	child_ctx[5] = list[i].stat;
	child_ctx[6] = list[i].description;
	return child_ctx;
}

// (57:4) {#each items as { icon, stat, description }}
function create_each_block$m(ctx) {
	let li;
	let div;
	let icon;
	let t0;
	let h3;
	let t1_value = /*stat*/ ctx[5] + "";
	let t1;
	let t2;
	let span;
	let t3_value = /*description*/ ctx[6] + "";
	let t3;
	let t4;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			li = element("li");
			div = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			h3 = element("h3");
			t1 = text(t1_value);
			t2 = space();
			span = element("span");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div = claim_element(li_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			claim_component(icon.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			h3 = claim_element(li_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, t1_value);
			h3_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			span = claim_element(li_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t3 = claim_text(span_nodes, t3_value);
			span_nodes.forEach(detach);
			t4 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "icon svelte-1psz6c1");
			attr(h3, "class", "stat svelte-1psz6c1");
			attr(span, "class", "description svelte-1psz6c1");
			attr(li, "class", "svelte-1psz6c1");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div);
			mount_component(icon, div, null);
			append_hydration(li, t0);
			append_hydration(li, h3);
			append_hydration(h3, t1);
			append_hydration(li, t2);
			append_hydration(li, span);
			append_hydration(span, t3);
			append_hydration(li, t4);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*items*/ 8) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);
			if ((!current || dirty & /*items*/ 8) && t1_value !== (t1_value = /*stat*/ ctx[5] + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*items*/ 8) && t3_value !== (t3_value = /*description*/ ctx[6] + "")) set_data(t3, t3_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$w(ctx) {
	let div1;
	let section;
	let div0;
	let span0;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let span1;
	let t4;
	let t5;
	let ul;
	let current;
	let each_value = /*items*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$m(get_each_context$m(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			span0 = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			span1 = element("span");
			t4 = text(/*subhead*/ ctx[2]);
			t5 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, /*superhead*/ ctx[0]);
			span0_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, /*subhead*/ ctx[2]);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "superhead");
			attr(h2, "class", "heading");
			attr(span1, "class", "subheading");
			attr(div0, "class", "heading-group svelte-1psz6c1");
			attr(ul, "class", "svelte-1psz6c1");
			attr(section, "class", "section-container svelte-1psz6c1");
			attr(div1, "class", "section");
			attr(div1, "id", "section-24664dd5");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(div0, t3);
			append_hydration(div0, span1);
			append_hydration(span1, t4);
			append_hydration(section, t5);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (!current || dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);
			if (!current || dirty & /*subhead*/ 4) set_data(t4, /*subhead*/ ctx[2]);

			if (dirty & /*items*/ 8) {
				each_value = /*items*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$m(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$m(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$v($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { subhead } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('subhead' in $$props) $$invalidate(2, subhead = $$props.subhead);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
	};

	return [superhead, heading, subhead, items];
}

class Component$w extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$v, create_fragment$w, safe_not_equal, {
			superhead: 0,
			heading: 1,
			subhead: 2,
			items: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$n(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i];
	return child_ctx;
}

// (100:10) {#if teaser.image.url}
function create_if_block_1$3(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*teaser*/ ctx[1].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*teaser*/ ctx[1].image.alt);
			attr(img, "class", "svelte-hgebdu");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 1 && !src_url_equal(img.src, img_src_value = /*teaser*/ ctx[1].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*teasers*/ 1 && img_alt_value !== (img_alt_value = /*teaser*/ ctx[1].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (106:12) {#if teaser.link.url}
function create_if_block$g(ctx) {
	let a;
	let t_value = /*teaser*/ ctx[1].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-hgebdu");
			attr(a, "href", a_href_value = /*teaser*/ ctx[1].link.url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*teasers*/ 1 && t_value !== (t_value = /*teaser*/ ctx[1].link.label + "")) set_data(t, t_value);

			if (dirty & /*teasers*/ 1 && a_href_value !== (a_href_value = /*teaser*/ ctx[1].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (98:6) {#each teasers as teaser}
function create_each_block$n(ctx) {
	let div2;
	let t0;
	let div1;
	let h2;
	let t1_value = /*teaser*/ ctx[1].title + "";
	let t1;
	let t2;
	let div0;
	let raw_value = /*teaser*/ ctx[1].body.html + "";
	let t3;
	let t4;
	let if_block0 = /*teaser*/ ctx[1].image.url && create_if_block_1$3(ctx);
	let if_block1 = /*teaser*/ ctx[1].link.url && create_if_block$g(ctx);

	return {
		c() {
			div2 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			div1 = element("div");
			h2 = element("h2");
			t1 = text(t1_value);
			t2 = space();
			div0 = element("div");
			t3 = space();
			if (if_block1) if_block1.c();
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block0) if_block0.l(div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, t1_value);
			h2_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-hgebdu");
			attr(div0, "class", "body svelte-hgebdu");
			attr(div1, "class", "content-section svelte-hgebdu");
			attr(div2, "class", "teaser svelte-hgebdu");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			if (if_block0) if_block0.m(div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t3);
			if (if_block1) if_block1.m(div1, null);
			append_hydration(div2, t4);
		},
		p(ctx, dirty) {
			if (/*teaser*/ ctx[1].image.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_1$3(ctx);
					if_block0.c();
					if_block0.m(div2, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (dirty & /*teasers*/ 1 && t1_value !== (t1_value = /*teaser*/ ctx[1].title + "")) set_data(t1, t1_value);
			if (dirty & /*teasers*/ 1 && raw_value !== (raw_value = /*teaser*/ ctx[1].body.html + "")) div0.innerHTML = raw_value;
			if (/*teaser*/ ctx[1].link.url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block$g(ctx);
					if_block1.c();
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function create_fragment$x(ctx) {
	let div2;
	let section;
	let div1;
	let div0;
	let each_value = /*teasers*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$n(get_each_context$n(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "teasers svelte-hgebdu");
			attr(div1, "class", "section-container svelte-hgebdu");
			attr(section, "class", "svelte-hgebdu");
			attr(div2, "class", "section");
			attr(div2, "id", "section-5f772dbe");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*teasers*/ 1) {
				each_value = /*teasers*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$n(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$n(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$w($$self, $$props, $$invalidate) {
	let { teasers } = $$props;

	$$self.$$set = $$props => {
		if ('teasers' in $$props) $$invalidate(0, teasers = $$props.teasers);
	};

	return [teasers];
}

class Component$x extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$w, create_fragment$x, safe_not_equal, { teasers: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$y(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-7037ku");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-8d6b0d83");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$x($$self, $$props, $$invalidate) {
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content];
}

class Component$y extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$x, create_fragment$y, safe_not_equal, { content: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$o(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].title;
	child_ctx[3] = list[i].links;
	return child_ctx;
}

function get_each_context_1$6(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].link;
	return child_ctx;
}

// (62:12) {#each links as { link }}
function create_each_block_1$6(ctx) {
	let li;
	let a;
	let t0_value = /*link*/ ctx[6].label + "";
	let t0;
	let a_href_value;
	let t1;

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-11gedy2");
			attr(a, "href", a_href_value = /*link*/ ctx[6].url);
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*menus*/ 2 && t0_value !== (t0_value = /*link*/ ctx[6].label + "")) set_data(t0, t0_value);

			if (dirty & /*menus*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[6].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (58:6) {#each menus as { title, links }}
function create_each_block$o(ctx) {
	let nav;
	let h3;
	let t0_value = /*title*/ ctx[2] + "";
	let t0;
	let t1;
	let ul;
	let t2;
	let each_value_1 = /*links*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$6(get_each_context_1$6(ctx, each_value_1, i));
	}

	return {
		c() {
			nav = element("nav");
			h3 = element("h3");
			t0 = text(t0_value);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", {});
			var nav_nodes = children(nav);
			h3 = claim_element(nav_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, t0_value);
			h3_nodes.forEach(detach);
			t1 = claim_space(nav_nodes);
			ul = claim_element(nav_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-11gedy2");
			attr(ul, "class", "svelte-11gedy2");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			append_hydration(nav, h3);
			append_hydration(h3, t0);
			append_hydration(nav, t1);
			append_hydration(nav, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(nav, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*menus*/ 2 && t0_value !== (t0_value = /*title*/ ctx[2] + "")) set_data(t0, t0_value);

			if (dirty & /*menus*/ 2) {
				each_value_1 = /*links*/ ctx[3];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$6(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$6(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$z(ctx) {
	let div3;
	let footer;
	let div2;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";
	let t;
	let div1;
	let each_value = /*menus*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$o(get_each_context$o(ctx, each_value, i));
	}

	return {
		c() {
			div3 = element("div");
			footer = element("footer");
			div2 = element("div");
			div0 = element("div");
			t = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			footer = claim_element(div3_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div2 = claim_element(footer_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "content svelte-11gedy2");
			attr(div1, "class", "nav-items svelte-11gedy2");
			attr(div2, "class", "section-container svelte-11gedy2");
			attr(footer, "class", "svelte-11gedy2");
			attr(div3, "class", "section");
			attr(div3, "id", "section-0e963563");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, footer);
			append_hydration(footer, div2);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*menus*/ 2) {
				each_value = /*menus*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$o(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$o(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$y($$self, $$props, $$invalidate) {
	let { content } = $$props;
	let { menus } = $$props;

	$$self.$$set = $$props => {
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
		if ('menus' in $$props) $$invalidate(1, menus = $$props.menus);
	};

	return [content, menus];
}

class Component$z extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$y, create_fragment$z, safe_not_equal, { content: 0, menus: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$A(ctx) {
	let div;
	let aside;
	let h3;
	let raw_value = /*quote*/ ctx[0].html + "";
	let t0;
	let span;
	let t1;

	return {
		c() {
			div = element("div");
			aside = element("aside");
			h3 = element("h3");
			t0 = space();
			span = element("span");
			t1 = text(/*attribution*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			aside = claim_element(div_nodes, "ASIDE", { class: true });
			var aside_nodes = children(aside);
			h3 = claim_element(aside_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			h3_nodes.forEach(detach);
			t0 = claim_space(aside_nodes);
			span = claim_element(aside_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, /*attribution*/ ctx[1]);
			span_nodes.forEach(detach);
			aside_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "heading svelte-1rprab5");
			attr(span, "class", "attribution");
			attr(aside, "class", "section-container svelte-1rprab5");
			attr(div, "class", "section");
			attr(div, "id", "section-54098366");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, aside);
			append_hydration(aside, h3);
			h3.innerHTML = raw_value;
			append_hydration(aside, t0);
			append_hydration(aside, span);
			append_hydration(span, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*quote*/ 1 && raw_value !== (raw_value = /*quote*/ ctx[0].html + "")) h3.innerHTML = raw_value;			if (dirty & /*attribution*/ 2) set_data(t1, /*attribution*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$z($$self, $$props, $$invalidate) {
	let { quote } = $$props;
	let { attribution } = $$props;

	$$self.$$set = $$props => {
		if ('quote' in $$props) $$invalidate(0, quote = $$props.quote);
		if ('attribution' in $$props) $$invalidate(1, attribution = $$props.attribution);
	};

	return [quote, attribution];
}

class Component$A extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$z, create_fragment$A, safe_not_equal, { quote: 0, attribution: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$p(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	child_ctx[9] = i;
	return child_ctx;
}

function get_each_context_1$7(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	child_ctx[9] = i;
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	return child_ctx;
}

// (130:8) {:else}
function create_else_block_1(ctx) {
	let span;
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			span = element("span");
			t = text(t_value);
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, t_value);
			span_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (128:8) {#if logo.image.url}
function create_if_block_2$1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (135:8) {#each site_nav as { link }}
function create_each_block_3(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "nav-item svelte-6vjs4t");
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (138:8) {#each cta as { link }
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "button svelte-6vjs4t");
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (149:4) {#if mobileNavOpen}
function create_if_block$h(ctx) {
	let nav;
	let t0;
	let t1;
	let hr;
	let t2;
	let t3;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].image.url) return create_if_block_1$4;
		return create_else_block$2;
	}

	let current_block_type = select_block_type_1(ctx);
	let if_block = current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$7(get_each_context_1$7(ctx, each_value_1, i));
	}

	let each_value = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$p(get_each_context$p(ctx, each_value, i));
	}

	icon = new Component$3({ props: { icon: "ph:x-duotone" } });

	return {
		c() {
			nav = element("nav");
			if_block.c();
			t0 = space();

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			hr = element("hr");
			t2 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);
			if_block.l(nav_nodes);
			t0 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			hr = claim_element(nav_nodes, "HR", { class: true });
			t2 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t3 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(hr, "class", "svelte-6vjs4t");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-6vjs4t");
			attr(nav, "id", "mobile-nav");
			attr(nav, "class", "svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			if_block.m(nav, null);
			append_hydration(nav, t0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, hr);
			append_hydration(nav, t2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t3);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type_1(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(nav, t0);
				}
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$7(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$7(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, t1);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*cta*/ 4) {
				each_value = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$p(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$p(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t3);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			if_block.d();
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (153:8) {:else}
function create_else_block$2(ctx) {
	let span;
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			span = element("span");
			t = text(t_value);
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, t_value);
			span_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (151:8) {#if logo.image.url}
function create_if_block_1$4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (156:8) {#each site_nav as { link }}
function create_each_block_1$7(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "class", "svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (160:8) {#each cta as { link }
function create_each_block$p(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "class", "button svelte-6vjs4t");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$B(ctx) {
	let div2;
	let header;
	let div1;
	let div0;
	let a;
	let style___size = `${/*logo*/ ctx[0].size}rem`;
	let t0;
	let nav;
	let t1;
	let t2;
	let button;
	let icon;
	let t3;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].image.url) return create_if_block_2$1;
		return create_else_block_1;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type(ctx);
	let each_value_3 = /*site_nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks_1[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	let each_value_2 = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	icon = new Component$3({ props: { icon: "ic:round-menu" } });
	let if_block1 = /*mobileNavOpen*/ ctx[3] && create_if_block$h(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div1 = element("div");
			div0 = element("div");
			a = element("a");
			if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			if_block0.l(a_nodes);
			a_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-6vjs4t");
			set_style(a, "--size", style___size);
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-6vjs4t");
			attr(nav, "class", "svelte-6vjs4t");
			attr(div0, "class", "desktop-nav svelte-6vjs4t");
			attr(div1, "class", "section-container svelte-6vjs4t");
			attr(header, "class", "svelte-6vjs4t");
			attr(div2, "class", "section");
			attr(div2, "id", "section-cd5dc256");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div1);
			append_hydration(div1, div0);
			append_hydration(div0, a);
			if_block0.m(a, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block1) if_block1.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if_block0.d(1);
				if_block0 = current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a, null);
				}
			}

			if (dirty & /*logo*/ 1 && style___size !== (style___size = `${/*logo*/ ctx[0].size}rem`)) {
				set_style(a, "--size", style___size);
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_3 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_3(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav, t1);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_3.length;
			}

			if (dirty & /*cta*/ 4) {
				each_value_2 = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t2);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_2.length;
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$h(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if_block0.d();
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (if_block1) if_block1.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$A($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { cta } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('cta' in $$props) $$invalidate(2, cta = $$props.cta);
	};

	return [logo, site_nav, cta, mobileNavOpen, click_handler, click_handler_1];
}

class Component$B extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$A, create_fragment$B, safe_not_equal, { logo: 0, site_nav: 1, cta: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_if_block$i(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(img, "class", "svelte-np59cr");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*image*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment$C(ctx) {
	let div5;
	let section;
	let div4;
	let div3;
	let div0;
	let icon;
	let t0;
	let div1;
	let raw_value = /*quote*/ ctx[0].html + "";
	let t1;
	let div2;
	let t2;
	let t3;
	let current;
	icon = new Component$3({ props: { icon: "fa:quote-left" } });
	let if_block = /*image*/ ctx[2].url && create_if_block$i(ctx);

	return {
		c() {
			div5 = element("div");
			section = element("section");
			div4 = element("div");
			div3 = element("div");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			div1 = element("div");
			t1 = space();
			div2 = element("div");
			t2 = text(/*name*/ ctx[1]);
			t3 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			section = claim_element(div5_nodes, "SECTION", {});
			var section_nodes = children(section);
			div4 = claim_element(section_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			t2 = claim_text(div2_nodes, /*name*/ ctx[1]);
			div2_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			if (if_block) if_block.l(div3_nodes);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-np59cr");
			attr(div1, "class", "quote svelte-np59cr");
			attr(div2, "class", "name");
			attr(div3, "class", "testimonial svelte-np59cr");
			attr(div4, "class", "section-container svelte-np59cr");
			attr(div5, "class", "section");
			attr(div5, "id", "section-3dc1020a");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, section);
			append_hydration(section, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div0);
			mount_component(icon, div0, null);
			append_hydration(div3, t0);
			append_hydration(div3, div1);
			div1.innerHTML = raw_value;
			append_hydration(div3, t1);
			append_hydration(div3, div2);
			append_hydration(div2, t2);
			append_hydration(div3, t3);
			if (if_block) if_block.m(div3, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if ((!current || dirty & /*quote*/ 1) && raw_value !== (raw_value = /*quote*/ ctx[0].html + "")) div1.innerHTML = raw_value;			if (!current || dirty & /*name*/ 2) set_data(t2, /*name*/ ctx[1]);

			if (/*image*/ ctx[2].url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$i(ctx);
					if_block.c();
					if_block.m(div3, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div5);
			destroy_component(icon);
			if (if_block) if_block.d();
		}
	};
}

function instance$B($$self, $$props, $$invalidate) {
	let { quote } = $$props;
	let { name } = $$props;
	let { image } = $$props;

	$$self.$$set = $$props => {
		if ('quote' in $$props) $$invalidate(0, quote = $$props.quote);
		if ('name' in $$props) $$invalidate(1, name = $$props.name);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
	};

	return [quote, name, image];
}

class Component$C extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$B, create_fragment$C, safe_not_equal, { quote: 0, name: 1, image: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$q(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].quote;
	child_ctx[4] = list[i].name;
	child_ctx[5] = list[i].subtitle;
	child_ctx[6] = list[i].image;
	child_ctx[8] = i;
	return child_ctx;
}

// (93:4) {#each testimonials as { quote, name, subtitle, image }
function create_each_block$q(ctx) {
	let li;
	let div0;
	let raw_value = /*quote*/ ctx[3].html + "";
	let div0_data_key_value;
	let t0;
	let div2;
	let img;
	let img_src_value;
	let img_alt_value;
	let t1;
	let div1;
	let span0;
	let t2_value = /*name*/ ctx[4] + "";
	let t2;
	let t3;
	let span1;
	let t4_value = /*subtitle*/ ctx[5] + "";
	let t4;
	let t5;

	return {
		c() {
			li = element("li");
			div0 = element("div");
			t0 = space();
			div2 = element("div");
			img = element("img");
			t1 = space();
			div1 = element("div");
			span0 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span1 = element("span");
			t4 = text(t4_value);
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true, "data-key": true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			img = claim_element(div2_nodes, "IMG", { src: true, alt: true, class: true });
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span0 = claim_element(div1_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t2 = claim_text(span0_nodes, t2_value);
			span0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			span1 = claim_element(div1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, t4_value);
			span1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "quote svelte-1u7vqb1");
			attr(div0, "data-key", div0_data_key_value = "testimonials[" + /*i*/ ctx[8] + "].quote");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[6].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[6].alt);
			attr(img, "class", "svelte-1u7vqb1");
			attr(span0, "class", "name svelte-1u7vqb1");
			attr(span1, "class", "subtitle svelte-1u7vqb1");
			attr(div1, "class", "text svelte-1u7vqb1");
			attr(div2, "class", "person svelte-1u7vqb1");
			attr(li, "class", "svelte-1u7vqb1");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			div0.innerHTML = raw_value;
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, img);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, span0);
			append_hydration(span0, t2);
			append_hydration(div1, t3);
			append_hydration(div1, span1);
			append_hydration(span1, t4);
			append_hydration(li, t5);
		},
		p(ctx, dirty) {
			if (dirty & /*testimonials*/ 4 && raw_value !== (raw_value = /*quote*/ ctx[3].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*testimonials*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[6].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*testimonials*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[6].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*testimonials*/ 4 && t2_value !== (t2_value = /*name*/ ctx[4] + "")) set_data(t2, t2_value);
			if (dirty & /*testimonials*/ 4 && t4_value !== (t4_value = /*subtitle*/ ctx[5] + "")) set_data(t4, t4_value);
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$D(ctx) {
	let div1;
	let section;
	let div0;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let ul;
	let each_value = /*testimonials*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$q(get_each_context$q(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead svelte-1u7vqb1");
			attr(h2, "class", "heading");
			attr(div0, "class", "heading-group svelte-1u7vqb1");
			attr(ul, "class", "svelte-1u7vqb1");
			attr(section, "class", "section-container svelte-1u7vqb1");
			attr(div1, "class", "section");
			attr(div1, "id", "section-edde4f96");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(section, t3);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);

			if (dirty & /*testimonials*/ 4) {
				each_value = /*testimonials*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$q(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$q(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$C($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('testimonials' in $$props) $$invalidate(2, testimonials = $$props.testimonials);
	};

	return [superhead, heading, testimonials];
}

class Component$D extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$C, create_fragment$D, safe_not_equal, {
			superhead: 0,
			heading: 1,
			testimonials: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$r(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].icon;
	child_ctx[4] = list[i].title;
	child_ctx[5] = list[i].description;
	return child_ctx;
}

// (121:6) {#each cards as { icon, title, description }}
function create_each_block$r(ctx) {
	let div1;
	let div0;
	let icon;
	let t0;
	let span0;
	let t1_value = /*title*/ ctx[4] + "";
	let t1;
	let t2;
	let span1;
	let t3_value = /*description*/ ctx[5] + "";
	let t3;
	let t4;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[3] } });

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			span0 = claim_element(div1_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			span1 = claim_element(div1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-m1wbya");
			attr(span0, "class", "title svelte-m1wbya");
			attr(span1, "class", "description svelte-m1wbya");
			attr(div1, "class", "card svelte-m1wbya");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			mount_component(icon, div0, null);
			append_hydration(div1, t0);
			append_hydration(div1, span0);
			append_hydration(span0, t1);
			append_hydration(div1, t2);
			append_hydration(div1, span1);
			append_hydration(span1, t3);
			append_hydration(div1, t4);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*cards*/ 4) icon_changes.icon = /*icon*/ ctx[3];
			icon.$set(icon_changes);
			if ((!current || dirty & /*cards*/ 4) && t1_value !== (t1_value = /*title*/ ctx[4] + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 4) && t3_value !== (t3_value = /*description*/ ctx[5] + "")) set_data(t3, t3_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_component(icon);
		}
	};
}

function create_fragment$E(ctx) {
	let div3;
	let section;
	let div2;
	let div0;
	let h2;
	let t0;
	let t1;
	let form_1;
	let input;
	let input_placeholder_value;
	let t2;
	let button;
	let t3_value = /*form*/ ctx[1].button_label + "";
	let t3;
	let t4;
	let span;
	let t5_value = /*form*/ ctx[1].footer + "";
	let t5;
	let t6;
	let div1;
	let current;
	let each_value = /*cards*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$r(get_each_context$r(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			form_1 = element("form");
			input = element("input");
			t2 = space();
			button = element("button");
			t3 = text(t3_value);
			t4 = space();
			span = element("span");
			t5 = text(t5_value);
			t6 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			form_1 = claim_element(div0_nodes, "FORM", { action: true, class: true });
			var form_1_nodes = children(form_1);

			input = claim_element(form_1_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			t2 = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t3 = claim_text(button_nodes, t3_value);
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			t4 = claim_space(div0_nodes);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t5 = claim_text(span_nodes, t5_value);
			span_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t6 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-m1wbya");
			attr(input, "type", "email");
			attr(input, "placeholder", input_placeholder_value = /*form*/ ctx[1].placeholder);
			attr(input, "class", "svelte-m1wbya");
			attr(button, "type", "button");
			attr(button, "class", "svelte-m1wbya");
			attr(form_1, "action", "");
			attr(form_1, "class", "svelte-m1wbya");
			attr(span, "class", "footer svelte-m1wbya");
			attr(div0, "class", "signup svelte-m1wbya");
			attr(div1, "class", "cards svelte-m1wbya");
			attr(div2, "class", "section-container svelte-m1wbya");
			attr(section, "class", "svelte-m1wbya");
			attr(div3, "class", "section");
			attr(div3, "id", "section-6358c722");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, form_1);
			append_hydration(form_1, input);
			append_hydration(form_1, t2);
			append_hydration(form_1, button);
			append_hydration(button, t3);
			append_hydration(div0, t4);
			append_hydration(div0, span);
			append_hydration(span, t5);
			append_hydration(div2, t6);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (!current || dirty & /*form*/ 2 && input_placeholder_value !== (input_placeholder_value = /*form*/ ctx[1].placeholder)) {
				attr(input, "placeholder", input_placeholder_value);
			}

			if ((!current || dirty & /*form*/ 2) && t3_value !== (t3_value = /*form*/ ctx[1].button_label + "")) set_data(t3, t3_value);
			if ((!current || dirty & /*form*/ 2) && t5_value !== (t5_value = /*form*/ ctx[1].footer + "")) set_data(t5, t5_value);

			if (dirty & /*cards*/ 4) {
				each_value = /*cards*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$r(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$r(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$D($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { form } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('form' in $$props) $$invalidate(1, form = $$props.form);
		if ('cards' in $$props) $$invalidate(2, cards = $$props.cards);
	};

	return [heading, form, cards];
}

class Component$E extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$D, create_fragment$E, safe_not_equal, { heading: 0, form: 1, cards: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$F(ctx) {
	let div1;
	let div0;
	let hr;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			hr = element("hr");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			hr = claim_element(div0_nodes, "HR", {});
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container svelte-1nxn5fd");
			attr(div1, "class", "section");
			attr(div1, "id", "section-bce6e337");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, hr);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

class Component$F extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$F, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$s(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i];
	return child_ctx;
}

function get_each_context_1$8(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].icon;
	child_ctx[8] = list[i].label;
	return child_ctx;
}

// (97:4) {#each icon_list as { icon, label }}
function create_each_block_1$8(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*label*/ ctx[8] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$3({ props: { icon: /*icon*/ ctx[7] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", {});
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-7sz6s1");
			attr(li, "class", "svelte-7sz6s1");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*icon_list*/ 4) icon_changes.icon = /*icon*/ ctx[7];
			icon.$set(icon_changes);
			if ((!current || dirty & /*icon_list*/ 4) && t1_value !== (t1_value = /*label*/ ctx[8] + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (107:4) {#each cards as card}
function create_each_block$s(ctx) {
	let li;
	let div0;
	let icon;
	let t0;
	let div2;
	let h3;
	let t1_value = /*card*/ ctx[4].title + "";
	let t1;
	let t2;
	let div1;
	let raw_value = /*card*/ ctx[4].content.html + "";
	let t3;
	let a;
	let span;
	let t4_value = /*card*/ ctx[4].link.label + "";
	let t4;
	let a_href_value;
	let t5;
	let current;
	icon = new Component$3({ props: { icon: /*card*/ ctx[4].icon } });

	return {
		c() {
			li = element("li");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			div2 = element("div");
			h3 = element("h3");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			t3 = space();
			a = element("a");
			span = element("span");
			t4 = text(t4_value);
			t5 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, t1_value);
			h3_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			a = claim_element(div2_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", {});
			var span_nodes = children(span);
			t4 = claim_text(span_nodes, t4_value);
			span_nodes.forEach(detach);
			a_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-7sz6s1");
			attr(h3, "class", "title svelte-7sz6s1");
			attr(div1, "class", "content svelte-7sz6s1");
			attr(a, "href", a_href_value = /*card*/ ctx[4].link.url);
			attr(a, "class", "link svelte-7sz6s1");
			attr(div2, "class", "body svelte-7sz6s1");
			attr(li, "class", "svelte-7sz6s1");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			mount_component(icon, div0, null);
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t1);
			append_hydration(div2, t2);
			append_hydration(div2, div1);
			div1.innerHTML = raw_value;
			append_hydration(div2, t3);
			append_hydration(div2, a);
			append_hydration(a, span);
			append_hydration(span, t4);
			append_hydration(li, t5);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*cards*/ 8) icon_changes.icon = /*card*/ ctx[4].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*cards*/ 8) && t1_value !== (t1_value = /*card*/ ctx[4].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 8) && raw_value !== (raw_value = /*card*/ ctx[4].content.html + "")) div1.innerHTML = raw_value;			if ((!current || dirty & /*cards*/ 8) && t4_value !== (t4_value = /*card*/ ctx[4].link.label + "")) set_data(t4, t4_value);

			if (!current || dirty & /*cards*/ 8 && a_href_value !== (a_href_value = /*card*/ ctx[4].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$G(ctx) {
	let div1;
	let section;
	let header;
	let h2;
	let t0;
	let div0;
	let t1;
	let t2;
	let ul0;
	let t3;
	let ul1;
	let current;
	let each_value_1 = /*icon_list*/ ctx[2];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$8(get_each_context_1$8(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks_1[i], 1, 1, () => {
		each_blocks_1[i] = null;
	});

	let each_value = /*cards*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$s(get_each_context$s(ctx, each_value, i));
	}

	const out_1 = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div1 = element("div");
			section = element("section");
			header = element("header");
			h2 = element("h2");
			t0 = space();
			div0 = element("div");
			t1 = text(/*subhead*/ ctx[1]);
			t2 = space();
			ul0 = element("ul");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t3 = space();
			ul1 = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			h2_nodes.forEach(detach);
			t0 = claim_space(header_nodes);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t1 = claim_text(div0_nodes, /*subhead*/ ctx[1]);
			div0_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			ul0 = claim_element(section_nodes, "UL", { class: true });
			var ul0_nodes = children(ul0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(ul0_nodes);
			}

			ul0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			ul1 = claim_element(section_nodes, "UL", { class: true });
			var ul1_nodes = children(ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul1_nodes);
			}

			ul1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-7sz6s1");
			attr(div0, "class", "subheading");
			attr(header, "class", "heading-group svelte-7sz6s1");
			attr(ul0, "class", "icon-list svelte-7sz6s1");
			attr(ul1, "class", "cards svelte-7sz6s1");
			attr(section, "class", "section-container svelte-7sz6s1");
			attr(div1, "class", "section");
			attr(div1, "id", "section-726c0803");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, header);
			append_hydration(header, h2);
			h2.innerHTML = /*heading*/ ctx[0];
			append_hydration(header, t0);
			append_hydration(header, div0);
			append_hydration(div0, t1);
			append_hydration(section, t2);
			append_hydration(section, ul0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(ul0, null);
				}
			}

			append_hydration(section, t3);
			append_hydration(section, ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul1, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) h2.innerHTML = /*heading*/ ctx[0];			if (!current || dirty & /*subhead*/ 2) set_data(t1, /*subhead*/ ctx[1]);

			if (dirty & /*icon_list*/ 4) {
				each_value_1 = /*icon_list*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$8(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
						transition_in(each_blocks_1[i], 1);
					} else {
						each_blocks_1[i] = create_each_block_1$8(child_ctx);
						each_blocks_1[i].c();
						transition_in(each_blocks_1[i], 1);
						each_blocks_1[i].m(ul0, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks_1.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (dirty & /*cards*/ 8) {
				each_value = /*cards*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$s(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$s(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out_1(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks_1[i]);
			}

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks_1 = each_blocks_1.filter(Boolean);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				transition_out(each_blocks_1[i]);
			}

			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$E($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subhead } = $$props;
	let { icon_list } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subhead' in $$props) $$invalidate(1, subhead = $$props.subhead);
		if ('icon_list' in $$props) $$invalidate(2, icon_list = $$props.icon_list);
		if ('cards' in $$props) $$invalidate(3, cards = $$props.cards);
	};

	return [heading, subhead, icon_list, cards];
}

class Component$G extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$E, create_fragment$G, safe_not_equal, {
			heading: 0,
			subhead: 1,
			icon_list: 2,
			cards: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$t(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].link;
	return child_ctx;
}

// (74:2) {#if background.url}
function create_if_block$j(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*background*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*background*/ ctx[3].alt);
			attr(img, "class", "svelte-1qt2bex");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*background*/ 8 && !src_url_equal(img.src, img_src_value = /*background*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*background*/ 8 && img_alt_value !== (img_alt_value = /*background*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (81:6) {#each buttons as { link }}
function create_each_block$t(ctx) {
	let a;
	let t_value = /*link*/ ctx[4].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[4].url);
			attr(a, "class", "button svelte-1qt2bex");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*buttons*/ 4 && t_value !== (t_value = /*link*/ ctx[4].label + "")) set_data(t, t_value);

			if (dirty & /*buttons*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[4].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$H(ctx) {
	let div2;
	let header;
	let t0;
	let div1;
	let h1;
	let t1;
	let t2;
	let span;
	let t3;
	let t4;
	let div0;
	let if_block = /*background*/ ctx[3].url && create_if_block$j(ctx);
	let each_value = /*buttons*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$t(get_each_context$t(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			header = element("header");
			if (if_block) if_block.c();
			t0 = space();
			div1 = element("div");
			h1 = element("h1");
			t1 = text(/*heading*/ ctx[0]);
			t2 = space();
			span = element("span");
			t3 = text(/*subheading*/ ctx[1]);
			t4 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			if (if_block) if_block.l(header_nodes);
			t0 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h1 = claim_element(div1_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t1 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			span = claim_element(div1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t3 = claim_text(span_nodes, /*subheading*/ ctx[1]);
			span_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "heading svelte-1qt2bex");
			attr(span, "class", "subheading svelte-1qt2bex");
			attr(div0, "class", "buttons svelte-1qt2bex");
			attr(div1, "class", "heading-group svelte-1qt2bex");
			attr(header, "class", "svelte-1qt2bex");
			attr(div2, "class", "section");
			attr(div2, "id", "section-9172e44b");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			if (if_block) if_block.m(header, null);
			append_hydration(header, t0);
			append_hydration(header, div1);
			append_hydration(div1, h1);
			append_hydration(h1, t1);
			append_hydration(div1, t2);
			append_hydration(div1, span);
			append_hydration(span, t3);
			append_hydration(div1, t4);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (/*background*/ ctx[3].url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$j(ctx);
					if_block.c();
					if_block.m(header, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*heading*/ 1) set_data(t1, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t3, /*subheading*/ ctx[1]);

			if (dirty & /*buttons*/ 4) {
				each_value = /*buttons*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$t(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$t(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$F($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { buttons } = $$props;
	let { background } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('buttons' in $$props) $$invalidate(2, buttons = $$props.buttons);
		if ('background' in $$props) $$invalidate(3, background = $$props.background);
	};

	return [heading, subheading, buttons, background];
}

class Component$H extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$F, create_fragment$H, safe_not_equal, {
			heading: 0,
			subheading: 1,
			buttons: 2,
			background: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$u(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].image;
	return child_ctx;
}

// (32:6) {#each items as {image}}
function create_each_block$u(ctx) {
	let div;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;

	return {
		c() {
			div = element("div");
			img = element("img");
			t = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			img = claim_element(div_nodes, "IMG", { src: true, alt: true });
			t = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(div, "class", "item svelte-1s5lign");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, img);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$I(ctx) {
	let div2;
	let section;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$u(get_each_context$u(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", {});
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1s5lign");
			attr(div0, "class", "items svelte-1s5lign");
			attr(div1, "class", "section-container");
			attr(div2, "class", "section");
			attr(div2, "id", "section-a66854e9");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$u(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$u(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$G($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [heading, items];
}

class Component$I extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$G, create_fragment$I, safe_not_equal, { heading: 0, items: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$v(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].image;
	return child_ctx;
}

// (59:6) {#each logos as {image}}
function create_each_block$v(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[4].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[4].alt);
			attr(img, "class", "svelte-10qyatf");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logos*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[4].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logos*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[4].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment$J(ctx) {
	let div2;
	let section;
	let div1;
	let header;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let div0;
	let div0_class_value;
	let each_value = /*logos*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$v(get_each_context$v(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			header = element("header");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", {});
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(header, "class", "heading-group svelte-10qyatf");
			attr(div0, "class", div0_class_value = "logos " + /*logo_size*/ ctx[3] + " svelte-10qyatf");
			attr(section, "class", "section-container svelte-10qyatf");
			attr(div2, "class", "section");
			attr(div2, "id", "section-82232cca");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, header);
			append_hydration(header, span);
			append_hydration(span, t0);
			append_hydration(header, t1);
			append_hydration(header, h2);
			append_hydration(h2, t2);
			append_hydration(div1, t3);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);

			if (dirty & /*logos*/ 4) {
				each_value = /*logos*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$v(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$v(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*logo_size*/ 8 && div0_class_value !== (div0_class_value = "logos " + /*logo_size*/ ctx[3] + " svelte-10qyatf")) {
				attr(div0, "class", div0_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$H($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { logos } = $$props;
	let { logo_size } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('logos' in $$props) $$invalidate(2, logos = $$props.logos);
		if ('logo_size' in $$props) $$invalidate(3, logo_size = $$props.logo_size);
	};

	return [superhead, heading, logos, logo_size];
}

class Component$J extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$H, create_fragment$J, safe_not_equal, {
			superhead: 0,
			heading: 1,
			logos: 2,
			logo_size: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$w(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (64:4) {#each cards as card}
function create_each_block$w(ctx) {
	let li;
	let div0;
	let icon;
	let t0;
	let div2;
	let h3;
	let t1_value = /*card*/ ctx[3].title + "";
	let t1;
	let t2;
	let div1;
	let raw_value = /*card*/ ctx[3].content.html + "";
	let t3;
	let current;
	icon = new Component$3({ props: { icon: /*card*/ ctx[3].icon } });

	return {
		c() {
			li = element("li");
			div0 = element("div");
			create_component(icon.$$.fragment);
			t0 = space();
			div2 = element("div");
			h3 = element("h3");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			t3 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div0 = claim_element(li_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			claim_component(icon.$$.fragment, div0_nodes);
			div0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			div2 = claim_element(li_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, t1_value);
			h3_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "icon svelte-1rjjrv0");
			attr(h3, "class", "title svelte-1rjjrv0");
			attr(div1, "class", "content svelte-1rjjrv0");
			attr(div2, "class", "body svelte-1rjjrv0");
			attr(li, "class", "svelte-1rjjrv0");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div0);
			mount_component(icon, div0, null);
			append_hydration(li, t0);
			append_hydration(li, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t1);
			append_hydration(div2, t2);
			append_hydration(div2, div1);
			div1.innerHTML = raw_value;
			append_hydration(li, t3);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*cards*/ 4) icon_changes.icon = /*card*/ ctx[3].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*cards*/ 4) && t1_value !== (t1_value = /*card*/ ctx[3].title + "")) set_data(t1, t1_value);
			if ((!current || dirty & /*cards*/ 4) && raw_value !== (raw_value = /*card*/ ctx[3].content.html + "")) div1.innerHTML = raw_value;		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$K(ctx) {
	let div;
	let section;
	let header;
	let p;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let ul;
	let current;
	let each_value = /*cards*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$w(get_each_context$w(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div = element("div");
			section = element("section");
			header = element("header");
			p = element("p");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			header = claim_element(section_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			p = claim_element(header_nodes, "P", { class: true });
			var p_nodes = children(p);
			t0 = claim_text(p_nodes, /*superhead*/ ctx[0]);
			p_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			h2 = claim_element(header_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "svelte-1rjjrv0");
			attr(h2, "class", "heading svelte-1rjjrv0");
			attr(header, "class", "heading-group svelte-1rjjrv0");
			attr(ul, "class", "cards svelte-1rjjrv0");
			attr(section, "class", "section-container svelte-1rjjrv0");
			attr(div, "class", "section svelte-1rjjrv0");
			attr(div, "id", "section-6685e7eb");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, header);
			append_hydration(header, p);
			append_hydration(p, t0);
			append_hydration(header, t1);
			append_hydration(header, h2);
			append_hydration(h2, t2);
			append_hydration(section, t3);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (!current || dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);

			if (dirty & /*cards*/ 4) {
				each_value = /*cards*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$w(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$w(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$I($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { cards } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('cards' in $$props) $$invalidate(2, cards = $$props.cards);
	};

	return [superhead, heading, cards];
}

class Component$K extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$I, create_fragment$K, safe_not_equal, { superhead: 0, heading: 1, cards: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$L(ctx) {
	let div2;
	let section;
	let div0;
	let span;
	let t0;
	let t1;
	let h2;
	let t2;
	let t3;
	let div1;
	let raw_value = /*content*/ ctx[2].html + "";

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div0 = element("div");
			span = element("span");
			t0 = text(/*superhead*/ ctx[0]);
			t1 = space();
			h2 = element("h2");
			t2 = text(/*heading*/ ctx[1]);
			t3 = space();
			div1 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span = claim_element(div0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, /*superhead*/ ctx[0]);
			span_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t2 = claim_text(h2_nodes, /*heading*/ ctx[1]);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "superhead");
			attr(h2, "class", "heading");
			attr(div0, "class", "heading-group svelte-1maz2r5");
			attr(div1, "class", "content svelte-1maz2r5");
			attr(section, "class", "section-container svelte-1maz2r5");
			attr(div2, "class", "section");
			attr(div2, "id", "section-ebd5967e");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div0);
			append_hydration(div0, span);
			append_hydration(span, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h2);
			append_hydration(h2, t2);
			append_hydration(section, t3);
			append_hydration(section, div1);
			div1.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*superhead*/ 1) set_data(t0, /*superhead*/ ctx[0]);
			if (dirty & /*heading*/ 2) set_data(t2, /*heading*/ ctx[1]);
			if (dirty & /*content*/ 4 && raw_value !== (raw_value = /*content*/ ctx[2].html + "")) div1.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$J($$self, $$props, $$invalidate) {
	let { superhead } = $$props;
	let { heading } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('superhead' in $$props) $$invalidate(0, superhead = $$props.superhead);
		if ('heading' in $$props) $$invalidate(1, heading = $$props.heading);
		if ('content' in $$props) $$invalidate(2, content = $$props.content);
	};

	return [superhead, heading, content];
}

class Component$L extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$J, create_fragment$L, safe_not_equal, { superhead: 0, heading: 1, content: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$x(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].label;
	child_ctx[5] = list[i].type;
	child_ctx[6] = list[i].placeholder;
	return child_ctx;
}

// (80:6) {:else}
function create_else_block$3(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[4] + "";
	let t0;
	let t1;
	let input;
	let input_type_value;
	let input_placeholder_value;

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			input = element("input");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(label_nodes);

			input = claim_element(label_nodes, "INPUT", {
				class: true,
				type: true,
				placeholder: true
			});

			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "label svelte-prx89c");
			attr(input, "class", "placeholder svelte-prx89c");
			attr(input, "type", input_type_value = /*type*/ ctx[5]);
			attr(input, "placeholder", input_placeholder_value = /*placeholder*/ ctx[6]);
			attr(label, "class", "svelte-prx89c");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(label, t1);
			append_hydration(label, input);
		},
		p(ctx, dirty) {
			if (dirty & /*inputs*/ 4 && t0_value !== (t0_value = /*label*/ ctx[4] + "")) set_data(t0, t0_value);

			if (dirty & /*inputs*/ 4 && input_type_value !== (input_type_value = /*type*/ ctx[5])) {
				attr(input, "type", input_type_value);
			}

			if (dirty & /*inputs*/ 4 && input_placeholder_value !== (input_placeholder_value = /*placeholder*/ ctx[6])) {
				attr(input, "placeholder", input_placeholder_value);
			}
		},
		d(detaching) {
			if (detaching) detach(label);
		}
	};
}

// (75:6) {#if type === "textarea"}
function create_if_block$k(ctx) {
	let label;
	let span;
	let t0_value = /*label*/ ctx[4] + "";
	let t0;
	let t1;
	let textarea;
	let textarea_type_value;
	let textarea_placeholder_value;

	return {
		c() {
			label = element("label");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			textarea = element("textarea");
			this.h();
		},
		l(nodes) {
			label = claim_element(nodes, "LABEL", { class: true });
			var label_nodes = children(label);
			span = claim_element(label_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(label_nodes);

			textarea = claim_element(label_nodes, "TEXTAREA", {
				class: true,
				type: true,
				placeholder: true
			});

			children(textarea).forEach(detach);
			label_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "label svelte-prx89c");
			attr(textarea, "class", "placeholder svelte-prx89c");
			attr(textarea, "type", textarea_type_value = /*type*/ ctx[5]);
			attr(textarea, "placeholder", textarea_placeholder_value = /*placeholder*/ ctx[6]);
			attr(label, "class", "svelte-prx89c");
		},
		m(target, anchor) {
			insert_hydration(target, label, anchor);
			append_hydration(label, span);
			append_hydration(span, t0);
			append_hydration(label, t1);
			append_hydration(label, textarea);
		},
		p(ctx, dirty) {
			if (dirty & /*inputs*/ 4 && t0_value !== (t0_value = /*label*/ ctx[4] + "")) set_data(t0, t0_value);

			if (dirty & /*inputs*/ 4 && textarea_type_value !== (textarea_type_value = /*type*/ ctx[5])) {
				attr(textarea, "type", textarea_type_value);
			}

			if (dirty & /*inputs*/ 4 && textarea_placeholder_value !== (textarea_placeholder_value = /*placeholder*/ ctx[6])) {
				attr(textarea, "placeholder", textarea_placeholder_value);
			}
		},
		d(detaching) {
			if (detaching) detach(label);
		}
	};
}

// (74:4) {#each inputs as { label, type, placeholder }}
function create_each_block$x(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*type*/ ctx[5] === "textarea") return create_if_block$k;
		return create_else_block$3;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment$M(ctx) {
	let div2;
	let section;
	let div1;
	let div0;
	let h2;
	let t0;
	let t1;
	let p;
	let t2;
	let t3;
	let form;
	let t4;
	let button;
	let t5;
	let mounted;
	let dispose;
	let each_value = /*inputs*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$x(get_each_context$x(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			p = element("p");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			form = element("form");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			button = element("button");
			t5 = text("Submit");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*subheading*/ ctx[1]);
			p_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			form = claim_element(div1_nodes, "FORM", { class: true });
			var form_nodes = children(form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(form_nodes);
			}

			t4 = claim_space(form_nodes);
			button = claim_element(form_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t5 = claim_text(button_nodes, "Submit");
			button_nodes.forEach(detach);
			form_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(p, "class", "subheaging");
			attr(div0, "class", "heading-group svelte-prx89c");
			attr(button, "type", "submit");
			attr(button, "class", "button svelte-prx89c");
			attr(form, "class", "svelte-prx89c");
			attr(div1, "class", "box svelte-prx89c");
			attr(section, "class", "section-container svelte-prx89c");
			attr(div2, "class", "section");
			attr(div2, "id", "section-b930b46a");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p);
			append_hydration(p, t2);
			append_hydration(div1, t3);
			append_hydration(div1, form);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(form, null);
				}
			}

			append_hydration(form, t4);
			append_hydration(form, button);
			append_hydration(button, t5);

			if (!mounted) {
				dispose = listen(form, "submit", prevent_default(/*submit_handler*/ ctx[3]));
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*inputs*/ 4) {
				each_value = /*inputs*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$x(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$x(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(form, t4);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance$K($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { subheading } = $$props;
	let { inputs } = $$props;

	const submit_handler = ({ target }) => {
		const data = new FormData(target); // send `data` to email service
	};

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('inputs' in $$props) $$invalidate(2, inputs = $$props.inputs);
	};

	return [heading, subheading, inputs, submit_handler];
}

class Component$M extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$K, create_fragment$M, safe_not_equal, { heading: 0, subheading: 1, inputs: 2 });
	}
}

/* generated by Svelte v3.58.0 */

class Component$N extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, null, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$N(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let t10;
	let component_11;
	let t11;
	let component_12;
	let t12;
	let component_13;
	let t13;
	let component_14;
	let t14;
	let component_15;
	let t15;
	let component_16;
	let t16;
	let component_17;
	let t17;
	let component_18;
	let t18;
	let component_19;
	let t19;
	let component_20;
	let t20;
	let component_21;
	let t21;
	let component_22;
	let t22;
	let component_23;
	let t23;
	let component_24;
	let t24;
	let component_25;
	let t25;
	let component_26;
	let t26;
	let component_27;
	let t27;
	let component_28;
	let t28;
	let component_29;
	let t29;
	let component_30;
	let t30;
	let component_31;
	let t31;
	let component_32;
	let t32;
	let component_33;
	let t33;
	let component_34;
	let t34;
	let component_35;
	let t35;
	let component_36;
	let t36;
	let component_37;
	let t37;
	let component_38;
	let t38;
	let component_39;
	let t39;
	let component_40;
	let t40;
	let component_41;
	let t41;
	let component_42;
	let t42;
	let component_43;
	let t43;
	let component_44;
	let t44;
	let component_45;
	let t45;
	let component_46;
	let t46;
	let component_47;
	let t47;
	let component_48;
	let current;
	component_0 = new Component({});

	component_1 = new Component$1({
			props: {
				heading: "Schedule Meetings in Minutes with Cali",
				subheading: "Get your meetings effortlessly organized with Cali. So you can spend more time on meeting people instead of scheduling meetings.",
				link: { "url": "/", "label": "Get Started" },
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1523240795612-9a054b0db644?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
					"url": "https://images.unsplash.com/photo-1523240795612-9a054b0db644?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
					"size": null
				},
				variation: ""
			}
		});

	component_2 = new Component$2({
			props: {
				heading: "Who we've worked with",
				items: [
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"url": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/6/69/Airbnb_Logo_B%C3%A9lo.svg/440px-Airbnb_Logo_B%C3%A9lo.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/6/69/Airbnb_Logo_B%C3%A9lo.svg/440px-Airbnb_Logo_B%C3%A9lo.svg.png",
							"size": null
						}
					}
				]
			}
		});

	component_3 = new Component$4({
			props: {
				heading: "Our People",
				people: [
					{
						"name": "Jean Johnson",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1636067344050-5a8cd8e56f6e?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"url": "https://images.unsplash.com/photo-1636067344050-5a8cd8e56f6e?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"size": null
						},
						"title": "Lead UX Designer",
						"social_links": [
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "officia" }
							},
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "consequat" }
							}
						]
					},
					{
						"name": "Creed Salem",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1604364721460-0cbc5866219d?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"url": "https://images.unsplash.com/photo-1604364721460-0cbc5866219d?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"size": null
						},
						"title": "Senior Developer",
						"social_links": [
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "esse" }
							},
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "quis" }
							}
						]
					},
					{
						"name": "Kye Samuel",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1524868313790-96da775e01ad?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"url": "https://images.unsplash.com/photo-1524868313790-96da775e01ad?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1770&q=80",
							"size": null
						},
						"title": "Marketing Strategist",
						"social_links": [
							{
								"icon": "mdi:linkedin",
								"link": {
									"url": "https://linkedin.com",
									"label": "Linkedin"
								}
							},
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "Twitter" }
							}
						]
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				heading: "Featured List",
				cards: [
					{
						"icon": "material-symbols:check-circle-rounded",
						"title": "Real-time Updates",
						"description": {
							"html": "<p>Stay ahead of the game with real-time updates on flight delays.</p>",
							"markdown": "Stay ahead of the game with real-time updates on flight delays."
						}
					},
					{
						"icon": "material-symbols:check-circle-rounded",
						"title": "In-app Booking",
						"description": {
							"html": "<p>Book your flights, hotels, and experiences directly through our app. </p>",
							"markdown": "Book your flights, hotels, and experiences directly through our app. "
						}
					},
					{
						"icon": "material-symbols:check-circle-rounded",
						"title": "24/7 Customer Support",
						"description": {
							"html": "<p>We're here for you, no matter where in the world you are. </p>",
							"markdown": "We're here for you, no matter where in the world you are. "
						}
					}
				]
			}
		});

	component_5 = new Component$6({
			props: {
				heading: "Get in touch",
				email: "info@general.com",
				social: [
					{
						"icon": "mdi:twitter",
						"link": { "url": "/", "label": "nisi" }
					},
					{
						"icon": "mdi:twitter",
						"link": { "url": "/", "label": "cupidatat" }
					}
				]
			}
		});

	component_6 = new Component$7({
			props: {
				heading: "Call to action of somekind.",
				body: {
					"html": "<p>Follow these steps to get rolling with our service. Watch the video to learn more or reach out if you have any questions.</p>",
					"markdown": "Follow these steps to get rolling with our service. Watch the video to learn more or reach out if you have any questions."
				},
				buttons: [
					{
						"icon": "Dolore laborum cillum",
						"link": { "url": "/", "label": "Watch video" }
					},
					{
						"icon": "Officia velit elit",
						"link": { "url": "/", "label": "Contact Us" }
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				heading: "Signup Form",
				body: {
					"html": "<p>Stay updated and never miss out! Join our newsletter by filling out this simple form. Subscribing to our newsletter means you'll be the first to hear about our latest news, exclusive offers, events, and exciting developments.</p>",
					"markdown": "Stay updated and never miss out! Join our newsletter by filling out this simple form. Subscribing to our newsletter means you'll be the first to hear about our latest news, exclusive offers, events, and exciting developments."
				},
				form: {
					"input_label": "Email Address",
					"submit_label": "Submit"
				}
			}
		});

	component_8 = new Component$9({
			props: {
				heading: "Contact Us",
				subheading: "Whether you have questions, feedback, or just want to say hello, we're always ready to hear from you. Please fill out the contact form, and we'll do our best to respond within 24-48 hours.",
				social: [
					{
						"icon": "mdi:github",
						"link": { "url": "/", "label": "Github" }
					},
					{
						"icon": "mdi:facebook",
						"link": { "url": "/", "label": "Facebook" }
					}
				],
				inputs: [
					{
						"type": "text",
						"label": "Name",
						"placeholder": "John Doe"
					},
					{
						"type": "email",
						"label": "Email",
						"placeholder": "johndoe@johndoe.com"
					}
				],
				submit_label: "Submit"
			}
		});

	component_9 = new Component$a({
			props: {
				heading: "Testimonials",
				testimonials: [
					{
						"name": "Sam Jenkins",
						"quote": {
							"html": "<p>Traveling has always been my passion, but planning and organizing the trip details? Not so much. That's where this incredible travel app comes in. From the moment I downloaded it, my travel experience was completely transformed.</p>",
							"markdown": "Traveling has always been my passion, but planning and organizing the trip details? Not so much. That's where this incredible travel app comes in. From the moment I downloaded it, my travel experience was completely transformed."
						},
						"title": "Fellow traveller"
					},
					{
						"name": "Non ullamco mollit",
						"quote": {
							"html": "<h1 id=\"thisissomemarkdown\">This is some markdown</h1>",
							"markdown": "# This is some markdown"
						},
						"title": "Do occaecat sunt"
					}
				]
			}
		});

	component_10 = new Component$b({
			props: {
				heading: "Pricing",
				subheading: "Free for everyone. Start for free and upgrade when you need to. ",
				tiers: [
					{
						"link": { "url": "/", "label": "Sign Up" },
						"price": { "numerator": "Free", "denominator": "" },
						"title": "Free",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Community Support"
							},
							{
								"icon": "mdi:check",
								"item": "Aliqua sunt lorem"
							}
						],
						"description": {
							"html": "<p>Nisl tincidunt eget nullam non nisi. A lacus vestibulum sed arcu non. Quis lectus nulla at volutpat diam ut. </p>",
							"markdown": "Nisl tincidunt eget nullam non nisi. A lacus vestibulum sed arcu non. Quis lectus nulla at volutpat diam ut. "
						}
					},
					{
						"link": { "url": "/", "label": "Purchase" },
						"price": {
							"numerator": "$100",
							"denominator": "/month"
						},
						"title": "Premium",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Priority Support"
							},
							{
								"icon": "mdi:check",
								"item": "Enim mollit adipisicing"
							}
						],
						"description": {
							"html": "<p>A lacus vestibulum sed arcu non. Quis lectus nulla at volutpat diam ut. In nibh mauris cursus mattis.</p>",
							"markdown": "A lacus vestibulum sed arcu non. Quis lectus nulla at volutpat diam ut. In nibh mauris cursus mattis."
						}
					}
				]
			}
		});

	component_11 = new Component$c({
			props: {
				superhead: "Pricing",
				heading: "There's a plan for everyone.",
				subheading: "Whether you just need to spin up a few projects or you want to take it to the next level. We have a plan for you.",
				tiers: [
					{
						"link": { "url": "/", "label": "Get Started" },
						"price": {
							"numerator": "$15",
							"denominator": "/month"
						},
						"title": "Individual",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Veniam ut esse"
							},
							{
								"icon": "mdi:check",
								"item": "Fugiat amet id"
							}
						],
						"description": {
							"html": "<p>Perfect for freelancers </p>",
							"markdown": "Perfect for freelancers "
						}
					},
					{
						"link": { "url": "/", "label": "Get Started" },
						"price": {
							"numerator": "$25",
							"denominator": "/month"
						},
						"title": "Business",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Voluptate est deserunt"
							},
							{
								"icon": "mdi:check",
								"item": "Pariatur pariatur ut"
							}
						],
						"description": {
							"html": "<p>Elit eu commodo elit excepteur aute sit sit laborum.</p>",
							"markdown": " Elit eu commodo elit excepteur aute sit sit laborum."
						}
					},
					{
						"link": { "url": "/", "label": "Contact Us" },
						"price": {
							"numerator": "$900",
							"denominator": "/annual"
						},
						"title": "Enterprise",
						"features": [
							{
								"icon": "mdi:check",
								"item": "Laboris sunt pariatur"
							},
							{
								"icon": "mdi:check",
								"item": "Velit ullamco laborum"
							}
						],
						"description": {
							"html": "<p>Commodo irure ad duis nulla anim incididunt. Aute aute laboris qui tempor pariatur duis labore minim.</p>",
							"markdown": "Commodo irure ad duis nulla anim incididunt. Aute aute laboris qui tempor pariatur duis labore minim."
						}
					}
				]
			}
		});

	component_12 = new Component$d({
			props: {
				heading: "What we're good at.",
				subheading: "",
				cards: [
					{
						"stat": "24/7",
						"title": "Customer Support"
					},
					{
						"stat": "400",
						"title": "Completed Projects"
					},
					{
						"stat": "50",
						"title": "Trusted Partners"
					}
				]
			}
		});

	component_13 = new Component$e({
			props: {
				heading: "Web Development & Design Services",
				subheading: "Everything you need to boost your online presence.",
				buttons: [
					{
						"link": { "url": "/", "label": "Set up a call" }
					},
					{
						"link": { "url": "/", "label": "Learn More" }
					}
				]
			}
		});

	component_14 = new Component$f({
			props: {
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1685430485423-f87889a8552f?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2350&q=80",
					"url": "https://images.unsplash.com/photo-1685430485423-f87889a8552f?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2350&q=80",
					"size": null
				},
				content: {
					"html": "<h1 id=\"joinusonourmission\">Join us on our mission</h1>\n<p>Through awareness, education, and direct action, we're working to combat climate change and protect our precious ecosystems. Together, we can make a difference.</p>\n<p>Since our founding, we've been at the forefront of environmental conservation. Our dedicated team of scientists, activists, and volunteers works tirelessly to protect endangered species, restore critical habitats, and educate the public about the urgency of climate action.</p>",
					"markdown": "# Join us on our mission\n\n Through awareness, education, and direct action, we're working to combat climate change and protect our precious ecosystems. Together, we can make a difference.\n\nSince our founding, we've been at the forefront of environmental conservation. Our dedicated team of scientists, activists, and volunteers works tirelessly to protect endangered species, restore critical habitats, and educate the public about the urgency of climate action."
				}
			}
		});

	component_15 = new Component$g({
			props: {
				heading: "Call to action of somekind.",
				body: {
					"html": "<p>Follow these steps to get rolling with our service. Watch the video to learn more or reach out if you have any questions.</p>",
					"markdown": "Follow these steps to get rolling with our service. Watch the video to learn more or reach out if you have any questions."
				},
				buttons: [
					{
						"icon": "Dolore laborum cillum",
						"link": { "url": "/", "label": "Watch video" }
					},
					{
						"icon": "Officia velit elit",
						"link": { "url": "/", "label": "Contact Us" }
					}
				]
			}
		});

	component_16 = new Component$h({
			props: {
				heading: "Get in touch",
				email: "info@general.com",
				social: [
					{
						"icon": "mdi:twitter",
						"link": { "url": "/", "label": "Twitter" }
					},
					{
						"icon": "mdi:facebook",
						"link": { "url": "/", "label": "cupidatat" }
					},
					{
						"icon": "mdi:reddit",
						"link": { "url": "/", "label": "Reddit" }
					}
				]
			}
		});

	component_17 = new Component$i({
			props: {
				heading: "Walkthrough",
				cards: [
					{
						"title": "Schedule a call",
						"subtitle": {
							"html": "<p>We'll walk you through our process and we'll answer any question you may have.</p>",
							"markdown": "We'll walk you through our process and we'll answer any question you may have."
						}
					},
					{
						"title": "We have a strategy meeting",
						"subtitle": {
							"html": "<p>We figure out your goals and mission and incorporate that into a plan.</p>",
							"markdown": "We figure out your goals and mission and incorporate that into a plan."
						}
					},
					{
						"title": "You're prepared to handle your stuff",
						"subtitle": {
							"html": "<p>Once we're done, you'll be ready to tackle anything.</p>",
							"markdown": "Once we're done, you'll be ready to tackle anything."
						}
					}
				],
				button: {
					"link": {
						"url": "/",
						"label": "Learn More",
						"active": false
					}
				}
			}
		});

	component_18 = new Component$j({
			props: {
				footer_links: [
					{
						"link": {
							"url": "/work",
							"label": "Work",
							"active": false
						}
					},
					{
						"link": {
							"url": "/services",
							"label": "Services",
							"active": false
						}
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				]
			}
		});

	component_19 = new Component$k({
			props: {
				heading: "Our Services",
				items: [
					{
						"title": "Design",
						"description": {
							"html": "<p>Contrary to popular belief, Lorem Ipsum is not simply random text. It has roots in a piece.</p>",
							"markdown": "Contrary to popular belief, Lorem Ipsum is not simply random text. It has roots in a piece."
						}
					},
					{
						"title": "Development",
						"description": {
							"html": "<p>The standard chunk of Lorem Ipsum used since the 1500s is reproduced below for those interested. </p>",
							"markdown": "The standard chunk of Lorem Ipsum used since the 1500s is reproduced below for those interested. "
						}
					},
					{
						"title": "UX & UI Architecture",
						"description": {
							"html": "<p>There are many variations of passages of Lorem Ipsum available, but the majority have suffered alteration in some form, by injected humour.</p>",
							"markdown": "There are many variations of passages of Lorem Ipsum available, but the majority have suffered alteration in some form, by injected humour."
						}
					},
					{
						"title": "SEO Optimization",
						"description": {
							"html": "<p>ll the Lorem Ipsum generators on the Internet tend to repeat predefined chunks as necessary.</p>",
							"markdown": "ll the Lorem Ipsum generators on the Internet tend to repeat predefined chunks as necessary."
						}
					},
					{
						"title": "Content Strategy",
						"description": {
							"html": "<p>The generated Lorem Ipsum is therefore always free from repetition, injected humour, or non-characteristic words etc.</p>",
							"markdown": "The generated Lorem Ipsum is therefore always free from repetition, injected humour, or non-characteristic words etc."
						}
					},
					{
						"title": "Testing & Maitenance ",
						"description": {
							"html": "<p>\"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt.</p>",
							"markdown": "\"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt."
						}
					}
				],
				variation: ""
			}
		});

	component_20 = new Component$l({
			props: {
				heading: "Who we've worked with",
				items: [
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-75' width='186' height='41' viewBox='0 0 186 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M59.0372 2.72868C59.0372 1.33929 60.1758 0.212959 61.5805 0.212959H66.0111C67.0108 0.212959 67.9797 0.555658 68.7527 1.18272L70.1005 2.276L70.1342 2.30641C70.1653 2.29603 70.1964 2.28589 70.2276 2.276C72.6592 1.50561 75.6094 1.3591 78.6205 1.3591C81.6316 1.3591 84.5818 1.50561 87.0134 2.276C87.0446 2.28589 87.0757 2.29603 87.1068 2.30641L87.1405 2.276L88.4883 1.18272C89.2613 0.555658 90.2302 0.212959 91.2299 0.212959H95.6605C97.0652 0.212959 98.2038 1.33929 98.2038 2.72868V4.28386C98.2038 5.48711 97.6914 6.6347 96.7922 7.4451L95.7049 8.42509C95.1741 8.90351 94.537 9.25169 93.845 9.44151L93.5878 9.51207C94.5953 11.89 95.1519 14.4318 95.1519 16.488C95.1519 24.7594 89.978 28.3317 85.4192 31.4793C81.8291 33.9581 78.6205 36.1734 78.6205 40.213C78.6205 36.1734 75.4119 33.9581 71.8218 31.4793C67.263 28.3317 62.0891 24.7594 62.0891 16.488C62.0891 14.4318 62.6457 11.89 63.6532 9.51207L63.396 9.44151C62.704 9.25169 62.0669 8.90351 61.5361 8.42509L60.4488 7.4451C59.5496 6.6347 59.0372 5.48711 59.0372 4.28386V2.72868ZM81.9268 23.2502C81.9268 23.6454 81.7526 24.0243 81.4426 24.3038C81.1326 24.5832 80.7121 24.7402 80.2736 24.7402C79.8951 24.7402 79.5299 24.6231 79.2377 24.4113C79.7351 25.7283 81.008 26.9762 82.9441 24.9694C84.6533 23.1047 82.8681 19.1718 81.1289 16.838C80.5492 16.0601 79.5975 15.6857 78.6205 15.6857C77.6435 15.6857 76.6918 16.0601 76.1121 16.838C74.3729 19.1718 72.5877 23.1047 74.2969 24.9694C76.233 26.9762 77.5059 25.7283 78.0033 24.4113C77.7111 24.6231 77.3459 24.7402 76.9674 24.7402C76.5289 24.7402 76.1084 24.5832 75.7984 24.3038C75.4884 24.0243 75.3142 23.6454 75.3142 23.2502H81.9268ZM72.2898 11.6081H67.6844L71.3139 14.4828C72.1126 15.1153 73.28 14.9131 73.7742 14.0566C74.3982 12.9752 73.5694 11.6081 72.2898 11.6081ZM84.9512 11.6081H89.5566L85.9271 14.4828C85.1284 15.1153 83.961 14.9131 83.4668 14.0566C82.8428 12.9752 83.6716 11.6081 84.9512 11.6081Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M103.69 28.5463H107.77V13.1563H103.69V28.5463ZM103.69 10.7563H107.77V7.09629H103.69V10.7563Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M110.399 33.5863H114.479V26.8063H114.539C115.409 28.1263 116.819 28.9963 118.979 28.9963C122.939 28.9963 125.639 25.8463 125.639 20.8663C125.639 16.0663 123.029 12.7363 118.949 12.7363C116.849 12.7363 115.409 13.7263 114.419 15.0763H114.329V13.1563H110.399V33.5863ZM118.109 25.6063C115.679 25.6063 114.389 23.7763 114.389 20.9863C114.389 18.2263 115.409 16.0363 117.959 16.0363C120.479 16.0363 121.499 18.0763 121.499 20.9863C121.499 23.8963 120.179 25.6063 118.109 25.6063Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M133.778 28.9963C137.618 28.9963 140.258 27.1363 140.258 24.0463C140.258 20.4463 137.408 19.7263 134.828 19.1863C132.638 18.7363 130.598 18.6163 130.598 17.2963C130.598 16.1863 131.648 15.5863 133.238 15.5863C134.978 15.5863 136.028 16.1863 136.208 17.8363H139.898C139.598 14.7463 137.348 12.7363 133.298 12.7363C129.788 12.7363 127.028 14.3263 127.028 17.6563C127.028 21.0163 129.728 21.7663 132.488 22.3063C134.588 22.7263 136.538 22.8763 136.538 24.3463C136.538 25.4263 135.518 26.1163 133.718 26.1163C131.888 26.1163 130.628 25.3363 130.358 23.5663H126.578C126.818 26.8363 129.308 28.9963 133.778 28.9963Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M155.749 28.5463V13.1563H151.669V22.0363C151.669 24.0763 150.499 25.5163 148.579 25.5163C146.839 25.5163 146.029 24.5263 146.029 22.7263V13.1563H141.979V23.4163C141.979 26.7763 143.899 28.9663 147.319 28.9663C149.479 28.9663 150.679 28.1563 151.729 26.7463H151.819V28.5463H155.749Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M158.388 28.5463H162.468V19.6063C162.468 17.5663 163.578 16.2463 165.228 16.2463C166.728 16.2463 167.598 17.1463 167.598 18.8863V28.5463H171.678V19.6063C171.678 17.5663 172.728 16.2463 174.438 16.2463C175.938 16.2463 176.808 17.1463 176.808 18.8863V28.5463H180.888V18.1963C180.888 14.8363 179.058 12.7363 175.818 12.7363C173.868 12.7363 172.248 13.7563 171.198 15.4363H171.138C170.388 13.8163 168.828 12.7363 166.878 12.7363C164.748 12.7363 163.248 13.8163 162.408 15.2263H162.318V13.1563H158.388V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.684082 28.5463H4.76408V7.09629H0.684082V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M14.7403 28.9963C19.5103 28.9963 22.7803 25.4563 22.7803 20.8663C22.7803 16.2763 19.5103 12.7363 14.7403 12.7363C9.97025 12.7363 6.70025 16.2763 6.70025 20.8663C6.70025 25.4563 9.97025 28.9963 14.7403 28.9963ZM14.7403 25.8763C12.2203 25.8763 10.8403 23.8663 10.8403 20.8663C10.8403 17.8663 12.2203 15.8263 14.7403 15.8263C17.2303 15.8263 18.6403 17.8663 18.6403 20.8663C18.6403 23.8663 17.2303 25.8763 14.7403 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M31.4568 33.7963C33.7368 33.7963 35.7168 33.2563 37.0068 32.0563C38.1468 31.0063 38.8368 29.5363 38.8368 27.3763V13.1563H34.9068V14.7763H34.8468C33.9168 13.4863 32.5068 12.7363 30.5868 12.7363C26.6868 12.7363 23.9268 15.6763 23.9268 20.2663C23.9268 24.9163 27.2868 27.6163 30.7068 27.6163C32.6568 27.6163 33.8268 26.8363 34.7268 25.8163H34.8168V27.4963C34.8168 29.5963 33.7068 30.7063 31.3968 30.7063C29.5068 30.7063 28.6368 29.9563 28.3068 28.9963H24.2568C24.6768 31.9963 27.2568 33.7963 31.4568 33.7963ZM31.3968 24.3463C29.2968 24.3463 27.9168 22.8163 27.9168 20.2063C27.9168 17.6263 29.2968 16.0063 31.3668 16.0063C33.8268 16.0063 35.0268 17.9263 35.0268 20.1763C35.0268 22.4563 33.9768 24.3463 31.3968 24.3463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.7539 28.9963C53.5239 28.9963 56.7939 25.4563 56.7939 20.8663C56.7939 16.2763 53.5239 12.7363 48.7539 12.7363C43.9839 12.7363 40.7139 16.2763 40.7139 20.8663C40.7139 25.4563 43.9839 28.9963 48.7539 28.9963ZM48.7539 25.8763C46.2339 25.8763 44.8539 23.8663 44.8539 20.8663C44.8539 17.8663 46.2339 15.8263 48.7539 15.8263C51.2439 15.8263 52.6539 17.8663 52.6539 20.8663C52.6539 23.8663 51.2439 25.8763 48.7539 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M180.704 9.79629C180.704 9.10593 181.263 8.54629 181.954 8.54629H184.454C185.144 8.54629 185.704 9.10593 185.704 9.79629C185.704 10.4866 185.144 11.0463 184.454 11.0463H181.954C181.263 11.0463 180.704 10.4866 180.704 9.79629Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-75' width='186' height='41' viewBox='0 0 186 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M59.0372 2.72868C59.0372 1.33929 60.1758 0.212959 61.5805 0.212959H66.0111C67.0108 0.212959 67.9797 0.555658 68.7527 1.18272L70.1005 2.276L70.1342 2.30641C70.1653 2.29603 70.1964 2.28589 70.2276 2.276C72.6592 1.50561 75.6094 1.3591 78.6205 1.3591C81.6316 1.3591 84.5818 1.50561 87.0134 2.276C87.0446 2.28589 87.0757 2.29603 87.1068 2.30641L87.1405 2.276L88.4883 1.18272C89.2613 0.555658 90.2302 0.212959 91.2299 0.212959H95.6605C97.0652 0.212959 98.2038 1.33929 98.2038 2.72868V4.28386C98.2038 5.48711 97.6914 6.6347 96.7922 7.4451L95.7049 8.42509C95.1741 8.90351 94.537 9.25169 93.845 9.44151L93.5878 9.51207C94.5953 11.89 95.1519 14.4318 95.1519 16.488C95.1519 24.7594 89.978 28.3317 85.4192 31.4793C81.8291 33.9581 78.6205 36.1734 78.6205 40.213C78.6205 36.1734 75.4119 33.9581 71.8218 31.4793C67.263 28.3317 62.0891 24.7594 62.0891 16.488C62.0891 14.4318 62.6457 11.89 63.6532 9.51207L63.396 9.44151C62.704 9.25169 62.0669 8.90351 61.5361 8.42509L60.4488 7.4451C59.5496 6.6347 59.0372 5.48711 59.0372 4.28386V2.72868ZM81.9268 23.2502C81.9268 23.6454 81.7526 24.0243 81.4426 24.3038C81.1326 24.5832 80.7121 24.7402 80.2736 24.7402C79.8951 24.7402 79.5299 24.6231 79.2377 24.4113C79.7351 25.7283 81.008 26.9762 82.9441 24.9694C84.6533 23.1047 82.8681 19.1718 81.1289 16.838C80.5492 16.0601 79.5975 15.6857 78.6205 15.6857C77.6435 15.6857 76.6918 16.0601 76.1121 16.838C74.3729 19.1718 72.5877 23.1047 74.2969 24.9694C76.233 26.9762 77.5059 25.7283 78.0033 24.4113C77.7111 24.6231 77.3459 24.7402 76.9674 24.7402C76.5289 24.7402 76.1084 24.5832 75.7984 24.3038C75.4884 24.0243 75.3142 23.6454 75.3142 23.2502H81.9268ZM72.2898 11.6081H67.6844L71.3139 14.4828C72.1126 15.1153 73.28 14.9131 73.7742 14.0566C74.3982 12.9752 73.5694 11.6081 72.2898 11.6081ZM84.9512 11.6081H89.5566L85.9271 14.4828C85.1284 15.1153 83.961 14.9131 83.4668 14.0566C82.8428 12.9752 83.6716 11.6081 84.9512 11.6081Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M103.69 28.5463H107.77V13.1563H103.69V28.5463ZM103.69 10.7563H107.77V7.09629H103.69V10.7563Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M110.399 33.5863H114.479V26.8063H114.539C115.409 28.1263 116.819 28.9963 118.979 28.9963C122.939 28.9963 125.639 25.8463 125.639 20.8663C125.639 16.0663 123.029 12.7363 118.949 12.7363C116.849 12.7363 115.409 13.7263 114.419 15.0763H114.329V13.1563H110.399V33.5863ZM118.109 25.6063C115.679 25.6063 114.389 23.7763 114.389 20.9863C114.389 18.2263 115.409 16.0363 117.959 16.0363C120.479 16.0363 121.499 18.0763 121.499 20.9863C121.499 23.8963 120.179 25.6063 118.109 25.6063Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M133.778 28.9963C137.618 28.9963 140.258 27.1363 140.258 24.0463C140.258 20.4463 137.408 19.7263 134.828 19.1863C132.638 18.7363 130.598 18.6163 130.598 17.2963C130.598 16.1863 131.648 15.5863 133.238 15.5863C134.978 15.5863 136.028 16.1863 136.208 17.8363H139.898C139.598 14.7463 137.348 12.7363 133.298 12.7363C129.788 12.7363 127.028 14.3263 127.028 17.6563C127.028 21.0163 129.728 21.7663 132.488 22.3063C134.588 22.7263 136.538 22.8763 136.538 24.3463C136.538 25.4263 135.518 26.1163 133.718 26.1163C131.888 26.1163 130.628 25.3363 130.358 23.5663H126.578C126.818 26.8363 129.308 28.9963 133.778 28.9963Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M155.749 28.5463V13.1563H151.669V22.0363C151.669 24.0763 150.499 25.5163 148.579 25.5163C146.839 25.5163 146.029 24.5263 146.029 22.7263V13.1563H141.979V23.4163C141.979 26.7763 143.899 28.9663 147.319 28.9663C149.479 28.9663 150.679 28.1563 151.729 26.7463H151.819V28.5463H155.749Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M158.388 28.5463H162.468V19.6063C162.468 17.5663 163.578 16.2463 165.228 16.2463C166.728 16.2463 167.598 17.1463 167.598 18.8863V28.5463H171.678V19.6063C171.678 17.5663 172.728 16.2463 174.438 16.2463C175.938 16.2463 176.808 17.1463 176.808 18.8863V28.5463H180.888V18.1963C180.888 14.8363 179.058 12.7363 175.818 12.7363C173.868 12.7363 172.248 13.7563 171.198 15.4363H171.138C170.388 13.8163 168.828 12.7363 166.878 12.7363C164.748 12.7363 163.248 13.8163 162.408 15.2263H162.318V13.1563H158.388V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.684082 28.5463H4.76408V7.09629H0.684082V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M14.7403 28.9963C19.5103 28.9963 22.7803 25.4563 22.7803 20.8663C22.7803 16.2763 19.5103 12.7363 14.7403 12.7363C9.97025 12.7363 6.70025 16.2763 6.70025 20.8663C6.70025 25.4563 9.97025 28.9963 14.7403 28.9963ZM14.7403 25.8763C12.2203 25.8763 10.8403 23.8663 10.8403 20.8663C10.8403 17.8663 12.2203 15.8263 14.7403 15.8263C17.2303 15.8263 18.6403 17.8663 18.6403 20.8663C18.6403 23.8663 17.2303 25.8763 14.7403 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M31.4568 33.7963C33.7368 33.7963 35.7168 33.2563 37.0068 32.0563C38.1468 31.0063 38.8368 29.5363 38.8368 27.3763V13.1563H34.9068V14.7763H34.8468C33.9168 13.4863 32.5068 12.7363 30.5868 12.7363C26.6868 12.7363 23.9268 15.6763 23.9268 20.2663C23.9268 24.9163 27.2868 27.6163 30.7068 27.6163C32.6568 27.6163 33.8268 26.8363 34.7268 25.8163H34.8168V27.4963C34.8168 29.5963 33.7068 30.7063 31.3968 30.7063C29.5068 30.7063 28.6368 29.9563 28.3068 28.9963H24.2568C24.6768 31.9963 27.2568 33.7963 31.4568 33.7963ZM31.3968 24.3463C29.2968 24.3463 27.9168 22.8163 27.9168 20.2063C27.9168 17.6263 29.2968 16.0063 31.3668 16.0063C33.8268 16.0063 35.0268 17.9263 35.0268 20.1763C35.0268 22.4563 33.9768 24.3463 31.3968 24.3463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.7539 28.9963C53.5239 28.9963 56.7939 25.4563 56.7939 20.8663C56.7939 16.2763 53.5239 12.7363 48.7539 12.7363C43.9839 12.7363 40.7139 16.2763 40.7139 20.8663C40.7139 25.4563 43.9839 28.9963 48.7539 28.9963ZM48.7539 25.8763C46.2339 25.8763 44.8539 23.8663 44.8539 20.8663C44.8539 17.8663 46.2339 15.8263 48.7539 15.8263C51.2439 15.8263 52.6539 17.8663 52.6539 20.8663C52.6539 23.8663 51.2439 25.8763 48.7539 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M180.704 9.79629C180.704 9.10593 181.263 8.54629 181.954 8.54629H184.454C185.144 8.54629 185.704 9.10593 185.704 9.79629C185.704 10.4866 185.144 11.0463 184.454 11.0463H181.954C181.263 11.0463 180.704 10.4866 180.704 9.79629Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-76' width='218' height='40' viewBox='0 0 218 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M122.355 29.5238H127.018V11.9352H122.355V29.5238ZM122.355 9.19238H127.018V5.00952H122.355V9.19238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M130.023 35.2838H134.686V27.5352H134.754C135.748 29.0438 137.36 30.0381 139.828 30.0381C144.354 30.0381 147.44 26.4381 147.44 20.7467C147.44 15.2609 144.457 11.4552 139.794 11.4552C137.394 11.4552 135.748 12.5867 134.617 14.1295H134.514V11.9352H130.023V35.2838ZM138.834 26.1638C136.057 26.1638 134.583 24.0724 134.583 20.8838C134.583 17.7295 135.748 15.2267 138.663 15.2267C141.543 15.2267 142.708 17.5581 142.708 20.8838C142.708 24.2095 141.2 26.1638 138.834 26.1638Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M156.741 30.0381C161.13 30.0381 164.147 27.9124 164.147 24.3809C164.147 20.2667 160.89 19.4438 157.941 18.8267C155.438 18.3124 153.107 18.1752 153.107 16.6667C153.107 15.3981 154.307 14.7124 156.124 14.7124C158.113 14.7124 159.313 15.3981 159.518 17.2838H163.735C163.393 13.7524 160.821 11.4552 156.193 11.4552C152.181 11.4552 149.027 13.2724 149.027 17.0781C149.027 20.9181 152.113 21.7752 155.267 22.3924C157.667 22.8724 159.895 23.0438 159.895 24.7238C159.895 25.9581 158.73 26.7467 156.673 26.7467C154.581 26.7467 153.141 25.8552 152.833 23.8324H148.513C148.787 27.5695 151.633 30.0381 156.741 30.0381Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M181.85 29.5238V11.9352H177.187V22.0838C177.187 24.4152 175.85 26.0609 173.656 26.0609C171.667 26.0609 170.742 24.9295 170.742 22.8724V11.9352H166.113V23.6609C166.113 27.5009 168.307 30.0038 172.216 30.0038C174.685 30.0038 176.056 29.0781 177.256 27.4667H177.359V29.5238H181.85Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M184.866 29.5238H189.529V19.3067C189.529 16.9752 190.798 15.4667 192.684 15.4667C194.398 15.4667 195.392 16.4952 195.392 18.4838V29.5238H200.055V19.3067C200.055 16.9752 201.255 15.4667 203.209 15.4667C204.924 15.4667 205.918 16.4952 205.918 18.4838V29.5238H210.581V17.6952C210.581 13.8552 208.489 11.4552 204.786 11.4552C202.558 11.4552 200.706 12.6209 199.506 14.5409H199.438C198.581 12.6895 196.798 11.4552 194.569 11.4552C192.135 11.4552 190.421 12.6895 189.461 14.3009H189.358V11.9352H184.866V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.824158 29.5238H5.48701V5.00952H0.824158V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M16.8884 30.0381C22.3398 30.0381 26.0769 25.9924 26.0769 20.7467C26.0769 15.5009 22.3398 11.4552 16.8884 11.4552C11.4369 11.4552 7.69978 15.5009 7.69978 20.7467C7.69978 25.9924 11.4369 30.0381 16.8884 30.0381ZM16.8884 26.4724C14.0084 26.4724 12.4312 24.1752 12.4312 20.7467C12.4312 17.3181 14.0084 14.9867 16.8884 14.9867C19.7341 14.9867 21.3455 17.3181 21.3455 20.7467C21.3455 24.1752 19.7341 26.4724 16.8884 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M35.993 35.5238C38.5987 35.5238 40.8616 34.9067 42.3358 33.5352C43.6387 32.3352 44.4273 30.6552 44.4273 28.1867V11.9352H39.9359V13.7867H39.8673C38.8044 12.3124 37.193 11.4552 34.9987 11.4552C30.5416 11.4552 27.3873 14.8152 27.3873 20.0609C27.3873 25.3752 31.2273 28.4609 35.1359 28.4609C37.3644 28.4609 38.7016 27.5695 39.7301 26.4038H39.833V28.3238C39.833 30.7238 38.5644 31.9924 35.9244 31.9924C33.7644 31.9924 32.7701 31.1352 32.393 30.0381H27.7644C28.2444 33.4667 31.193 35.5238 35.993 35.5238ZM35.9244 24.7238C33.5244 24.7238 31.9473 22.9752 31.9473 19.9924C31.9473 17.0438 33.5244 15.1924 35.8901 15.1924C38.7016 15.1924 40.073 17.3867 40.073 19.9581C40.073 22.5638 38.873 24.7238 35.9244 24.7238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M55.7611 30.0381C61.2125 30.0381 64.9497 25.9924 64.9497 20.7467C64.9497 15.5009 61.2125 11.4552 55.7611 11.4552C50.3097 11.4552 46.5725 15.5009 46.5725 20.7467C46.5725 25.9924 50.3097 30.0381 55.7611 30.0381ZM55.7611 26.4724C52.8811 26.4724 51.304 24.1752 51.304 20.7467C51.304 17.3181 52.8811 14.9867 55.7611 14.9867C58.6068 14.9867 60.2183 17.3181 60.2183 20.7467C60.2183 24.1752 58.6068 26.4724 55.7611 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M212.275 9.04762C212.275 8.25864 212.915 7.61905 213.704 7.61905H216.561C217.35 7.61905 217.99 8.25864 217.99 9.04762C217.99 9.8366 217.35 10.4762 216.561 10.4762H213.704C212.915 10.4762 212.275 9.8366 212.275 9.04762Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M93.2277 0C104.273 0 113.228 8.95431 113.228 20C113.228 31.0457 104.273 40 93.2277 40C82.182 40 73.2277 31.0457 73.2277 20C73.2277 8.95431 82.182 0 93.2277 0ZM92.5048 1.49659C90.2231 1.81769 88.0505 3.65108 86.364 6.7174C85.8748 7.60683 85.4334 8.58946 85.0488 9.65044C87.342 9.07417 89.8611 8.73442 92.5048 8.68187V1.49659ZM83.3584 10.1308C83.8368 8.62958 84.4219 7.2484 85.0972 6.02065C85.9332 4.50059 86.9254 3.18795 88.0433 2.17977C81.9644 3.94523 77.1729 8.73679 75.4074 14.8157C76.4156 13.6978 77.7282 12.7056 79.2483 11.8696C80.4761 11.1943 81.8572 10.6091 83.3584 10.1308ZM82.8781 11.8211C82.3018 14.1143 81.9621 16.6334 81.9095 19.2771H74.7242C75.0453 16.9954 76.8787 14.8228 79.9451 13.1364C80.8345 12.6472 81.8171 12.2058 82.8781 11.8211ZM83.3556 19.2771C83.4153 16.392 83.8307 13.6834 84.5179 11.2902C86.9111 10.603 89.6197 10.1876 92.5048 10.1279V13.2508C91.4285 16.0062 89.2333 18.2012 86.4778 19.2771H83.3556ZM81.9095 20.7229H74.7242C75.0453 23.0046 76.8787 25.1771 79.9451 26.8636C80.8345 27.3528 81.8171 27.7942 82.8781 28.1789C82.3018 25.8857 81.9621 23.3666 81.9095 20.7229ZM84.5179 28.7098C83.8307 26.3166 83.4153 23.608 83.3556 20.7229H86.4778C89.2333 21.7988 91.4285 23.9938 92.5048 26.7492V29.8721C89.6197 29.8124 86.9111 29.397 84.5179 28.7098ZM83.3584 29.8692C81.8572 29.3909 80.4761 28.8057 79.2483 28.1304C77.7282 27.2944 76.4156 26.3022 75.4074 25.1843C77.1729 31.2632 81.9644 36.0548 88.0433 37.8202C86.9254 36.812 85.9332 35.4994 85.0972 33.9793C84.4219 32.7516 83.8368 31.3704 83.3584 29.8692ZM92.5048 38.5034C90.2231 38.1823 88.0505 36.3489 86.364 33.2826C85.8748 32.3932 85.4334 31.4105 85.0488 30.3496C87.342 30.9258 89.8611 31.2656 92.5048 31.3181V38.5034ZM98.412 37.8202C99.5299 36.812 100.522 35.4994 101.358 33.9793C102.033 32.7516 102.619 31.3704 103.097 29.8692C104.598 29.3909 105.979 28.8057 107.207 28.1304C108.727 27.2944 110.04 26.3022 111.048 25.1843C109.282 31.2632 104.491 36.0548 98.412 37.8202ZM101.407 30.3496C101.022 31.4105 100.58 32.3932 100.091 33.2826C98.4048 36.3489 96.2322 38.1823 93.9505 38.5034V31.3181C96.5942 31.2656 99.1133 30.9258 101.407 30.3496ZM103.577 28.1789C104.638 27.7942 105.621 27.3528 106.51 26.8636C109.577 25.1772 111.41 23.0046 111.731 20.7229H104.546C104.493 23.3666 104.153 25.8857 103.577 28.1789ZM103.1 20.7229C103.04 23.608 102.625 26.3166 101.937 28.7098C99.5442 29.397 96.8356 29.8124 93.9505 29.8721V26.7515C95.0265 23.9951 97.2222 21.7991 99.9784 20.7229H103.1ZM104.546 19.2771H111.731C111.41 16.9954 109.577 14.8228 106.51 13.1364C105.621 12.6472 104.638 12.2058 103.577 11.8211C104.153 14.1143 104.493 16.6334 104.546 19.2771ZM101.937 11.2902C102.625 13.6834 103.04 16.392 103.1 19.2771H99.9785C97.2222 18.2009 95.0265 16.0049 93.9505 13.2485V10.1279C96.8356 10.1876 99.5442 10.603 101.937 11.2902ZM103.097 10.1308C104.598 10.6091 105.979 11.1943 107.207 11.8696C108.727 12.7056 110.04 13.6978 111.048 14.8157C109.282 8.73679 104.491 3.94523 98.412 2.17977C99.5299 3.18795 100.522 4.50059 101.358 6.02065C102.033 7.2484 102.619 8.62958 103.097 10.1308ZM93.9505 1.49659C96.2322 1.81769 98.4048 3.65108 100.091 6.7174C100.58 7.60684 101.022 8.58946 101.407 9.65044C99.1133 9.07417 96.5942 8.73442 93.9505 8.68187V1.49659Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-76' width='218' height='40' viewBox='0 0 218 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M122.355 29.5238H127.018V11.9352H122.355V29.5238ZM122.355 9.19238H127.018V5.00952H122.355V9.19238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M130.023 35.2838H134.686V27.5352H134.754C135.748 29.0438 137.36 30.0381 139.828 30.0381C144.354 30.0381 147.44 26.4381 147.44 20.7467C147.44 15.2609 144.457 11.4552 139.794 11.4552C137.394 11.4552 135.748 12.5867 134.617 14.1295H134.514V11.9352H130.023V35.2838ZM138.834 26.1638C136.057 26.1638 134.583 24.0724 134.583 20.8838C134.583 17.7295 135.748 15.2267 138.663 15.2267C141.543 15.2267 142.708 17.5581 142.708 20.8838C142.708 24.2095 141.2 26.1638 138.834 26.1638Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M156.741 30.0381C161.13 30.0381 164.147 27.9124 164.147 24.3809C164.147 20.2667 160.89 19.4438 157.941 18.8267C155.438 18.3124 153.107 18.1752 153.107 16.6667C153.107 15.3981 154.307 14.7124 156.124 14.7124C158.113 14.7124 159.313 15.3981 159.518 17.2838H163.735C163.393 13.7524 160.821 11.4552 156.193 11.4552C152.181 11.4552 149.027 13.2724 149.027 17.0781C149.027 20.9181 152.113 21.7752 155.267 22.3924C157.667 22.8724 159.895 23.0438 159.895 24.7238C159.895 25.9581 158.73 26.7467 156.673 26.7467C154.581 26.7467 153.141 25.8552 152.833 23.8324H148.513C148.787 27.5695 151.633 30.0381 156.741 30.0381Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M181.85 29.5238V11.9352H177.187V22.0838C177.187 24.4152 175.85 26.0609 173.656 26.0609C171.667 26.0609 170.742 24.9295 170.742 22.8724V11.9352H166.113V23.6609C166.113 27.5009 168.307 30.0038 172.216 30.0038C174.685 30.0038 176.056 29.0781 177.256 27.4667H177.359V29.5238H181.85Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M184.866 29.5238H189.529V19.3067C189.529 16.9752 190.798 15.4667 192.684 15.4667C194.398 15.4667 195.392 16.4952 195.392 18.4838V29.5238H200.055V19.3067C200.055 16.9752 201.255 15.4667 203.209 15.4667C204.924 15.4667 205.918 16.4952 205.918 18.4838V29.5238H210.581V17.6952C210.581 13.8552 208.489 11.4552 204.786 11.4552C202.558 11.4552 200.706 12.6209 199.506 14.5409H199.438C198.581 12.6895 196.798 11.4552 194.569 11.4552C192.135 11.4552 190.421 12.6895 189.461 14.3009H189.358V11.9352H184.866V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.824158 29.5238H5.48701V5.00952H0.824158V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M16.8884 30.0381C22.3398 30.0381 26.0769 25.9924 26.0769 20.7467C26.0769 15.5009 22.3398 11.4552 16.8884 11.4552C11.4369 11.4552 7.69978 15.5009 7.69978 20.7467C7.69978 25.9924 11.4369 30.0381 16.8884 30.0381ZM16.8884 26.4724C14.0084 26.4724 12.4312 24.1752 12.4312 20.7467C12.4312 17.3181 14.0084 14.9867 16.8884 14.9867C19.7341 14.9867 21.3455 17.3181 21.3455 20.7467C21.3455 24.1752 19.7341 26.4724 16.8884 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M35.993 35.5238C38.5987 35.5238 40.8616 34.9067 42.3358 33.5352C43.6387 32.3352 44.4273 30.6552 44.4273 28.1867V11.9352H39.9359V13.7867H39.8673C38.8044 12.3124 37.193 11.4552 34.9987 11.4552C30.5416 11.4552 27.3873 14.8152 27.3873 20.0609C27.3873 25.3752 31.2273 28.4609 35.1359 28.4609C37.3644 28.4609 38.7016 27.5695 39.7301 26.4038H39.833V28.3238C39.833 30.7238 38.5644 31.9924 35.9244 31.9924C33.7644 31.9924 32.7701 31.1352 32.393 30.0381H27.7644C28.2444 33.4667 31.193 35.5238 35.993 35.5238ZM35.9244 24.7238C33.5244 24.7238 31.9473 22.9752 31.9473 19.9924C31.9473 17.0438 33.5244 15.1924 35.8901 15.1924C38.7016 15.1924 40.073 17.3867 40.073 19.9581C40.073 22.5638 38.873 24.7238 35.9244 24.7238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M55.7611 30.0381C61.2125 30.0381 64.9497 25.9924 64.9497 20.7467C64.9497 15.5009 61.2125 11.4552 55.7611 11.4552C50.3097 11.4552 46.5725 15.5009 46.5725 20.7467C46.5725 25.9924 50.3097 30.0381 55.7611 30.0381ZM55.7611 26.4724C52.8811 26.4724 51.304 24.1752 51.304 20.7467C51.304 17.3181 52.8811 14.9867 55.7611 14.9867C58.6068 14.9867 60.2183 17.3181 60.2183 20.7467C60.2183 24.1752 58.6068 26.4724 55.7611 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M212.275 9.04762C212.275 8.25864 212.915 7.61905 213.704 7.61905H216.561C217.35 7.61905 217.99 8.25864 217.99 9.04762C217.99 9.8366 217.35 10.4762 216.561 10.4762H213.704C212.915 10.4762 212.275 9.8366 212.275 9.04762Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M93.2277 0C104.273 0 113.228 8.95431 113.228 20C113.228 31.0457 104.273 40 93.2277 40C82.182 40 73.2277 31.0457 73.2277 20C73.2277 8.95431 82.182 0 93.2277 0ZM92.5048 1.49659C90.2231 1.81769 88.0505 3.65108 86.364 6.7174C85.8748 7.60683 85.4334 8.58946 85.0488 9.65044C87.342 9.07417 89.8611 8.73442 92.5048 8.68187V1.49659ZM83.3584 10.1308C83.8368 8.62958 84.4219 7.2484 85.0972 6.02065C85.9332 4.50059 86.9254 3.18795 88.0433 2.17977C81.9644 3.94523 77.1729 8.73679 75.4074 14.8157C76.4156 13.6978 77.7282 12.7056 79.2483 11.8696C80.4761 11.1943 81.8572 10.6091 83.3584 10.1308ZM82.8781 11.8211C82.3018 14.1143 81.9621 16.6334 81.9095 19.2771H74.7242C75.0453 16.9954 76.8787 14.8228 79.9451 13.1364C80.8345 12.6472 81.8171 12.2058 82.8781 11.8211ZM83.3556 19.2771C83.4153 16.392 83.8307 13.6834 84.5179 11.2902C86.9111 10.603 89.6197 10.1876 92.5048 10.1279V13.2508C91.4285 16.0062 89.2333 18.2012 86.4778 19.2771H83.3556ZM81.9095 20.7229H74.7242C75.0453 23.0046 76.8787 25.1771 79.9451 26.8636C80.8345 27.3528 81.8171 27.7942 82.8781 28.1789C82.3018 25.8857 81.9621 23.3666 81.9095 20.7229ZM84.5179 28.7098C83.8307 26.3166 83.4153 23.608 83.3556 20.7229H86.4778C89.2333 21.7988 91.4285 23.9938 92.5048 26.7492V29.8721C89.6197 29.8124 86.9111 29.397 84.5179 28.7098ZM83.3584 29.8692C81.8572 29.3909 80.4761 28.8057 79.2483 28.1304C77.7282 27.2944 76.4156 26.3022 75.4074 25.1843C77.1729 31.2632 81.9644 36.0548 88.0433 37.8202C86.9254 36.812 85.9332 35.4994 85.0972 33.9793C84.4219 32.7516 83.8368 31.3704 83.3584 29.8692ZM92.5048 38.5034C90.2231 38.1823 88.0505 36.3489 86.364 33.2826C85.8748 32.3932 85.4334 31.4105 85.0488 30.3496C87.342 30.9258 89.8611 31.2656 92.5048 31.3181V38.5034ZM98.412 37.8202C99.5299 36.812 100.522 35.4994 101.358 33.9793C102.033 32.7516 102.619 31.3704 103.097 29.8692C104.598 29.3909 105.979 28.8057 107.207 28.1304C108.727 27.2944 110.04 26.3022 111.048 25.1843C109.282 31.2632 104.491 36.0548 98.412 37.8202ZM101.407 30.3496C101.022 31.4105 100.58 32.3932 100.091 33.2826C98.4048 36.3489 96.2322 38.1823 93.9505 38.5034V31.3181C96.5942 31.2656 99.1133 30.9258 101.407 30.3496ZM103.577 28.1789C104.638 27.7942 105.621 27.3528 106.51 26.8636C109.577 25.1772 111.41 23.0046 111.731 20.7229H104.546C104.493 23.3666 104.153 25.8857 103.577 28.1789ZM103.1 20.7229C103.04 23.608 102.625 26.3166 101.937 28.7098C99.5442 29.397 96.8356 29.8124 93.9505 29.8721V26.7515C95.0265 23.9951 97.2222 21.7991 99.9784 20.7229H103.1ZM104.546 19.2771H111.731C111.41 16.9954 109.577 14.8228 106.51 13.1364C105.621 12.6472 104.638 12.2058 103.577 11.8211C104.153 14.1143 104.493 16.6334 104.546 19.2771ZM101.937 11.2902C102.625 13.6834 103.04 16.392 103.1 19.2771H99.9785C97.2222 18.2009 95.0265 16.0049 93.9505 13.2485V10.1279C96.8356 10.1876 99.5442 10.603 101.937 11.2902ZM103.097 10.1308C104.598 10.6091 105.979 11.1943 107.207 11.8696C108.727 12.7056 110.04 13.6978 111.048 14.8157C109.282 8.73679 104.491 3.94523 98.412 2.17977C99.5299 3.18795 100.522 4.50059 101.358 6.02065C102.033 7.2484 102.619 8.62958 103.097 10.1308ZM93.9505 1.49659C96.2322 1.81769 98.4048 3.65108 100.091 6.7174C100.58 7.60684 101.022 8.58946 101.407 9.65044C99.1133 9.07417 96.5942 8.73442 93.9505 8.68187V1.49659Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-74' width='70' height='44' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-74' width='70' height='44' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					}
				]
			}
		});

	component_21 = new Component$m({
			props: {
				headline: "Design something beautiful & functional."
			}
		});

	component_22 = new Component$n({
			props: {
				heading: "Frequently Asked Questions",
				items: [
					{
						"title": "What if I don't want to continue?",
						"description": {
							"html": "<p>You can cancel at anytime.</p>",
							"markdown": "You can cancel at anytime."
						}
					},
					{
						"title": "How much will this cost?",
						"description": {
							"html": "<p>Generally our services range from $100-500 depending on your needs.</p>",
							"markdown": "Generally our services range from $100-500 depending on your needs."
						}
					}
				]
			}
		});

	component_23 = new Component$o({
			props: {
				background: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1523627430842-015d8b38ce69?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2690&q=80",
					"url": "https://images.unsplash.com/photo-1523627430842-015d8b38ce69?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2690&q=80",
					"size": null
				},
				headline: "We were made for more.",
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Logo"
				},
				site_nav: [
					{
						"link": {
							"url": "/about",
							"label": "About",
							"active": false
						}
					},
					{
						"link": {
							"url": "/mission",
							"label": "Mission",
							"active": false
						}
					},
					{
						"link": { "url": "/team", "label": "Team" }
					},
					{
						"link": { "url": "/blog", "label": "Blog" }
					}
				]
			}
		});

	component_24 = new Component$p({
			props: {
				teasers: [
					{
						"link": { "url": "/", "label": "Read more" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1499951360447-b19be8fe80f5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
							"url": "https://images.unsplash.com/photo-1499951360447-b19be8fe80f5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2070&q=80",
							"size": null
						},
						"title": "Real-time collaboration",
						"content": {
							"html": "<p>Instant updates to your calendar without having to go through a third party app.</p>",
							"markdown": "Instant updates to your calendar without having to go through a third party app."
						}
					},
					{
						"link": { "url": "/", "label": "Learn More" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1521737852567-6949f3f9f2b5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2047&q=80",
							"url": "https://images.unsplash.com/photo-1521737852567-6949f3f9f2b5?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2047&q=80",
							"size": null
						},
						"title": "Endless integrations",
						"content": {
							"html": "<p>Integrate your google calendar and any other third-party calendar. Everything in one place.</p>",
							"markdown": "Integrate your google calendar and any other third-party calendar. Everything in one place."
						}
					}
				]
			}
		});

	component_25 = new Component$q({
			props: {
				heading: "Our Mission",
				link: { "url": "/mission", "label": "Donate" },
				content: {
					"html": "<p>Our mission is to safeguard the Earth: its people, its plants and animals, and the natural systems on which all life depends.</p>",
					"markdown": "Our mission is to safeguard the Earth: its people, its plants and animals, and the natural systems on which all life depends."
				}
			}
		});

	component_26 = new Component$r({
			props: {
				heading: "Our Team",
				people: [
					{
						"name": "Lisa Lane",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1525992979185-b214b603e97f?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=987&q=80",
							"url": "https://images.unsplash.com/photo-1525992979185-b214b603e97f?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=987&q=80",
							"size": null
						},
						"title": "Designer",
						"social_links": [
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "in" }
							},
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "consequat" }
							}
						]
					},
					{
						"name": "Talia Tuz",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1440178536296-c1041e136dda?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
							"url": "https://images.unsplash.com/photo-1440178536296-c1041e136dda?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
							"size": null
						},
						"title": "Editor",
						"social_links": [
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "amet" }
							},
							{
								"icon": "mdi:twitter",
								"link": { "url": "/", "label": "aliqua" }
							}
						]
					},
					{
						"name": "Gray Nelly",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1549068142-ffe6a519b2cd?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
							"url": "https://images.unsplash.com/photo-1549068142-ffe6a519b2cd?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
							"size": null
						},
						"title": "Co-editor",
						"social_links": [
							{
								"icon": "Laboris magna et",
								"link": { "url": "/", "label": "quis" }
							},
							{
								"icon": "Magna officia commodo",
								"link": { "url": "/", "label": "occaecat" }
							}
						]
					}
				]
			}
		});

	component_27 = new Component$s({
			props: {
				items: [
					{
						"link": {
							"url": "mailto:info@co.com",
							"label": "info@co.com"
						},
						"title": "Inquiries"
					},
					{
						"link": {
							"url": "mailto:partnerships@co.com",
							"label": "parterships@co.com"
						},
						"title": "Partnerships"
					}
				]
			}
		});

	component_28 = new Component$t({
			props: {
				items: [
					{
						"link": { "url": "/", "label": "eu" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1686062095898-de61c74f2a2e?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2232&q=80",
							"url": "https://images.unsplash.com/photo-1686062095898-de61c74f2a2e?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2232&q=80",
							"size": null
						},
						"title": "Abstract",
						"description": "Abstract photography invites viewers to interpret and engage with the image in their own unique way."
					},
					{
						"link": { "url": "/", "label": "consequat" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1686062096176-bfd55776c915?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2232&q=80",
							"url": "https://images.unsplash.com/photo-1686062096176-bfd55776c915?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2232&q=80",
							"size": null
						},
						"title": "Landscape",
						"description": " Landscape photography showcases the beauty and grandeur of natural environments, capturing expansive vistas and dramatic lighting."
					}
				]
			}
		});

	component_29 = new Component$u({
			props: {
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1531226208074-94fb5a1bb26c?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
					"url": "https://images.unsplash.com/photo-1531226208074-94fb5a1bb26c?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2370&q=80",
					"size": null
				}
			}
		});

	component_30 = new Component$v({
			props: {
				superhead: "October 21, 2023",
				heading: "Surviving the dark night",
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1537819191377-d3305ffddce4?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1642&q=80",
					"url": "https://images.unsplash.com/photo-1537819191377-d3305ffddce4?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1642&q=80",
					"size": null
				}
			}
		});

	component_31 = new Component$w({
			props: {
				superhead: "Our stats",
				heading: "We've put in alot of work to get where we are.",
				subhead: "",
				items: [
					{
						"icon": "mdi:home",
						"stat": "3.9M",
						"description": "Qui proident esse"
					},
					{
						"icon": "mdi:home",
						"stat": "3.9M",
						"description": "Aliquip quis ex"
					},
					{
						"icon": "mdi:clock",
						"stat": "1H",
						"description": "Less than an hour response time"
					}
				]
			}
		});

	component_32 = new Component$x({
			props: {
				teasers: [
					{
						"body": {
							"html": "<p>We are a beacon of commitment towards preserving our forests. In the embrace of nature, we stand steadfast, advocating for the voiceless sentinels of our ecosystem. Together, we forge a path towards a greener tomorrow.</p>",
							"markdown": "We are a beacon of commitment towards preserving our forests. In the embrace of nature, we stand steadfast, advocating for the voiceless sentinels of our ecosystem. Together, we forge a path towards a greener tomorrow."
						},
						"link": { "url": "/", "label": "Learn More" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1685189219324-a4ca49a306bd?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2148&q=80",
							"url": "https://images.unsplash.com/photo-1685189219324-a4ca49a306bd?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2148&q=80",
							"size": null
						},
						"title": "Community"
					},
					{
						"body": {
							"html": "<p>Eager to leave a green footprint? Lend your hands to Lorem Ipsum Dolor. Each seed you sow, every forest you help clean, and every conversation you initiate about the importance of trees, echoes in our mission. Every action matters!</p>",
							"markdown": "Eager to leave a green footprint? Lend your hands to Lorem Ipsum Dolor. Each seed you sow, every forest you help clean, and every conversation you initiate about the importance of trees, echoes in our mission. Every action matters!"
						},
						"link": { "url": "/", "label": "Learn More" },
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1685378751992-c9b2c6e85f61?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2831&q=80",
							"url": "https://images.unsplash.com/photo-1685378751992-c9b2c6e85f61?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=2831&q=80",
							"size": null
						},
						"title": "Volunteering"
					}
				]
			}
		});

	component_33 = new Component$y({
			props: {
				content: {
					"html": "<h1 id=\"heading1\">heading 1</h1>\n<p>Overall, our calendar software is the <em>perfect tool</em> for managing your time and staying organized. With its user-friendly interface and powerful search functionality, it's the ideal solution for anyone looking to take control of their schedule and make the most of their time.</p>\n<h2 id=\"heading2\">heading 2</h2>\n<p>Additionally, our software integrates seamlessly with <mark>popular email services,</mark></p>\n<p>so that users can easily invite others and receive updates about events.</p>\n<h3 id=\"heading3\">heading 3</h3>\n<p>Try it out today and see the difference for yourself. Overall, our calendar software is a comprehensive and effective tool for managing your time.</p>\n<blockquote>\n  <p>Some interesting quote info</p>\n</blockquote>",
					"markdown": "# heading 1\n\nOverall, our calendar software is the *perfect tool* for managing your time and staying organized. With its user-friendly interface and powerful search functionality, it's the ideal solution for anyone looking to take control of their schedule and make the most of their time.\n\n## heading 2\n\nAdditionally, our software integrates seamlessly with <mark>popular email services,</mark>\n\n so that users can easily invite others and receive updates about events.\n\n### heading 3\n\nTry it out today and see the difference for yourself. Overall, our calendar software is a comprehensive and effective tool for managing your time.\n\n> Some interesting quote info\n"
				}
			}
		});

	component_34 = new Component$z({
			props: {
				content: {
					"html": "<h3>BillionTrees <br></h3><p>321 Something St. Jackson, AL 20332</p>",
					"markdown": "### BillionTrees <br>\n\n\n\n321 Something St. Jackson, AL 20332\n\n"
				},
				menus: [
					{
						"links": [
							{ "link": { "url": "/", "label": "blog" } },
							{
								"link": { "url": "/", "label": "consectetur" }
							}
						],
						"title": "About Us"
					},
					{
						"links": [
							{ "link": { "url": "/", "label": "qui" } },
							{ "link": { "url": "/", "label": "ex" } }
						],
						"title": "Get Involved"
					}
				]
			}
		});

	component_35 = new Component$A({
			props: {
				quote: {
					"html": "<p>\"To be without trees would, in the most literal way, to be without our roots.\"</p>",
					"markdown": "\"To be without trees would, in the most literal way, to be without our roots.\"\n\n"
				},
				attribution: "-somebody somewhere"
			}
		});

	component_36 = new Component$B({
			props: {
				logo: {
					"size": "8",
					"image": {
						"alt": "Logoipsum",
						"src": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
						"url": "data:image/svg+xml,%3Csvg id='logo-53' width='169' height='42' viewBox='0 0 169 42' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath d='M50.8601 29.3532H62.8121V25.7532H55.1081V12.1932H50.8601V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M69.8932 26.9532C68.1892 26.9532 67.3012 25.4652 67.3012 23.2332C67.3012 21.0012 68.1892 19.4892 69.8932 19.4892C71.5972 19.4892 72.5092 21.0012 72.5092 23.2332C72.5092 25.4652 71.5972 26.9532 69.8932 26.9532ZM69.9172 29.7372C73.8772 29.7372 76.4692 26.9292 76.4692 23.2332C76.4692 19.5372 73.8772 16.7292 69.9172 16.7292C65.9812 16.7292 63.3412 19.5372 63.3412 23.2332C63.3412 26.9292 65.9812 29.7372 69.9172 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M83.3237 33.6012C85.1477 33.6012 86.7557 33.1932 87.8357 32.2332C88.8197 31.3452 89.4677 30.0012 89.4677 28.1532V17.0652H85.7237V18.3852H85.6757C84.9557 17.3532 83.8517 16.7052 82.2197 16.7052C79.1717 16.7052 77.0597 19.2492 77.0597 22.8492C77.0597 26.6172 79.6277 28.6812 82.3877 28.6812C83.8757 28.6812 84.8117 28.0812 85.5317 27.2652H85.6277V28.4892C85.6277 29.9772 84.9317 30.8412 83.2757 30.8412C81.9797 30.8412 81.3317 30.2892 81.1157 29.6412H77.3237C77.7077 32.2092 79.9397 33.6012 83.3237 33.6012ZM83.2997 25.7772C81.8357 25.7772 80.8757 24.5772 80.8757 22.7292C80.8757 20.8572 81.8357 19.6572 83.2997 19.6572C84.9317 19.6572 85.7957 21.0492 85.7957 22.7052C85.7957 24.4332 85.0037 25.7772 83.2997 25.7772Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M97.166 26.9532C95.462 26.9532 94.574 25.4652 94.574 23.2332C94.574 21.0012 95.462 19.4892 97.166 19.4892C98.87 19.4892 99.782 21.0012 99.782 23.2332C99.782 25.4652 98.87 26.9532 97.166 26.9532ZM97.19 29.7372C101.15 29.7372 103.742 26.9292 103.742 23.2332C103.742 19.5372 101.15 16.7292 97.19 16.7292C93.254 16.7292 90.614 19.5372 90.614 23.2332C90.614 26.9292 93.254 29.7372 97.19 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M104.884 29.3532H108.796V17.0652H104.884V29.3532ZM104.884 15.3612H108.796V12.1932H104.884V15.3612Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M110.494 33.4092H114.406V28.0812H114.454C115.222 29.1132 116.35 29.7372 117.934 29.7372C121.15 29.7372 123.286 27.1932 123.286 23.2092C123.286 19.5132 121.294 16.7052 118.03 16.7052C116.35 16.7052 115.15 17.4492 114.31 18.5532H114.238V17.0652H110.494V33.4092ZM116.926 26.7132C115.246 26.7132 114.286 25.3452 114.286 23.3532C114.286 21.3612 115.15 19.8492 116.854 19.8492C118.534 19.8492 119.326 21.2412 119.326 23.3532C119.326 25.4412 118.414 26.7132 116.926 26.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M129.655 29.7372C132.871 29.7372 135.247 28.3452 135.247 25.6572C135.247 22.5132 132.703 21.9612 130.543 21.6012C128.983 21.3132 127.591 21.1932 127.591 20.3292C127.591 19.5612 128.335 19.2012 129.295 19.2012C130.375 19.2012 131.119 19.5372 131.263 20.6412H134.863C134.671 18.2172 132.799 16.7052 129.319 16.7052C126.415 16.7052 124.015 18.0492 124.015 20.6412C124.015 23.5212 126.295 24.0972 128.431 24.4572C130.063 24.7452 131.551 24.8652 131.551 25.9692C131.551 26.7612 130.807 27.1932 129.631 27.1932C128.335 27.1932 127.519 26.5932 127.375 25.3692H123.679C123.799 28.0812 126.055 29.7372 129.655 29.7372Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M140.561 29.7132C142.265 29.7132 143.345 29.0412 144.233 27.8412H144.305V29.3532H148.049V17.0652H144.137V23.9292C144.137 25.3932 143.321 26.4012 141.977 26.4012C140.729 26.4012 140.129 25.6572 140.129 24.3132V17.0652H136.241V25.1292C136.241 27.8652 137.729 29.7132 140.561 29.7132Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath d='M149.75 29.3532H153.662V22.4652C153.662 21.0012 154.382 19.9692 155.606 19.9692C156.782 19.9692 157.334 20.7372 157.334 22.0572V29.3532H161.246V22.4652C161.246 21.0012 161.942 19.9692 163.19 19.9692C164.366 19.9692 164.918 20.7372 164.918 22.0572V29.3532H168.83V21.3612C168.83 18.6012 167.438 16.7052 164.654 16.7052C163.07 16.7052 161.75 17.3772 160.79 18.8652H160.742C160.118 17.5452 158.894 16.7052 157.286 16.7052C155.51 16.7052 154.334 17.5452 153.566 18.8172H153.494V17.0652H149.75V29.3532Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3Cpath fill-rule='evenodd' clip-rule='evenodd' d='M20.6842 0.961929C31.946 0.961929 41.0755 10.0914 41.0755 21.3532C41.0755 32.6151 31.946 41.7446 20.6842 41.7446C9.42234 41.7446 0.292847 32.6151 0.292847 21.3532C0.292847 10.0914 9.42234 0.961929 20.6842 0.961929ZM40.2928 21.3532C40.2928 10.5237 31.5137 1.74455 20.6842 1.74455C19.8106 1.74455 18.9505 1.80167 18.1071 1.91238C18.652 1.86474 19.2034 1.84042 19.7606 1.84042C30.1088 1.84042 38.4977 10.2293 38.4977 20.5775C38.4977 30.9256 30.1088 39.3145 19.7606 39.3145C9.96366 39.3145 1.92284 31.7956 1.09401 22.2135C1.54426 32.6439 10.1428 40.9619 20.6842 40.9619C31.5137 40.9619 40.2928 32.1828 40.2928 21.3532ZM37.715 20.5775C37.715 10.6615 29.6766 2.62305 19.7606 2.62305C18.9555 2.62305 18.1627 2.67605 17.3856 2.77874C17.8641 2.73848 18.3482 2.71794 18.8371 2.71794C28.2717 2.71794 35.9199 10.3662 35.9199 19.8007C35.9199 29.2353 28.2717 36.8835 18.8371 36.8835C9.91648 36.8835 2.59287 30.0458 1.8215 21.3256C2.21369 30.8946 10.0953 38.5319 19.7606 38.5319C29.6766 38.5319 37.715 30.4934 37.715 20.5775ZM18.8371 3.50057C27.8394 3.50057 35.1373 10.7984 35.1373 19.8007C35.1373 28.803 27.8394 36.1008 18.8371 36.1008C10.0434 36.1008 2.87602 29.1372 2.54867 20.4235C3.25542 28.2885 9.86471 34.4524 17.9137 34.4524C26.434 34.4524 33.3412 27.5453 33.3412 19.0249C33.3412 10.5045 26.434 3.59741 17.9137 3.59741C17.4729 3.59741 17.0364 3.6159 16.605 3.65213C17.3348 3.5522 18.0799 3.50057 18.8371 3.50057ZM32.5585 19.0249C32.5585 10.9368 26.0018 4.38004 17.9137 4.38004C17.2303 4.38004 16.5578 4.42684 15.8994 4.51742C16.2589 4.48928 16.6223 4.47495 16.9891 4.47495C24.5959 4.47495 30.7624 10.6414 30.7624 18.2482C30.7624 25.8549 24.5959 32.0214 16.9891 32.0214C9.82947 32.0214 3.94576 26.5585 3.27885 19.5736C3.56738 27.4075 10.0092 33.6698 17.9137 33.6698C26.0018 33.6698 32.5585 27.1131 32.5585 19.0249ZM16.9891 5.25757C24.1636 5.25757 29.9797 11.0737 29.9797 18.2482C29.9797 25.4227 24.1636 31.2388 16.9891 31.2388C9.95594 31.2388 4.2282 25.6496 4.00526 18.6706C4.60739 24.8008 9.77718 29.5904 16.0656 29.5904C22.7588 29.5904 28.1846 24.1645 28.1846 17.4714C28.1846 10.7783 22.7588 5.35246 16.0656 5.35246C15.7587 5.35246 15.4544 5.36387 15.1532 5.38629C15.753 5.30145 16.3659 5.25757 16.9891 5.25757ZM27.402 17.4714C27.402 11.2105 22.3265 6.13509 16.0656 6.13509C15.4941 6.13509 14.9325 6.17738 14.3837 6.259C14.6342 6.24106 14.8871 6.23193 15.1422 6.23193C20.9211 6.23193 25.6059 10.9167 25.6059 16.6956C25.6059 22.4746 20.9211 27.1593 15.1422 27.1593C9.72697 27.1593 5.27257 23.0458 4.73324 17.773C4.89313 23.8945 9.90561 28.8078 16.0656 28.8078C22.3265 28.8078 27.402 23.7323 27.402 17.4714ZM15.1422 7.01456C20.4889 7.01456 24.8232 11.3489 24.8232 16.6956C24.8232 22.0424 20.4889 26.3767 15.1422 26.3767C9.86348 26.3767 5.57156 22.152 5.46317 16.8993C5.9508 21.3032 9.68475 24.7283 14.2187 24.7283C19.084 24.7283 23.0281 20.7842 23.0281 15.9189C23.0281 11.0536 19.084 7.10945 14.2187 7.10945C14.0326 7.10945 13.8479 7.11522 13.6647 7.12659C14.1464 7.05282 14.6398 7.01456 15.1422 7.01456ZM22.2455 15.9189C22.2455 11.4858 18.6518 7.89208 14.2187 7.89208C13.7735 7.89208 13.3368 7.92832 12.9113 7.99801C13.0381 7.99133 13.1657 7.98795 13.2942 7.98795C17.2458 7.98795 20.4493 11.1914 20.4493 15.1431C20.4493 19.0948 17.2458 22.2983 13.2942 22.2983C9.64023 22.2983 6.626 19.5593 6.19252 16.0225C6.24802 20.4079 9.8202 23.9457 14.2187 23.9457C18.6518 23.9457 22.2455 20.352 22.2455 15.9189ZM13.2942 8.77057C16.8136 8.77057 19.6667 11.6236 19.6667 15.1431C19.6667 18.6626 16.8136 21.5156 13.2942 21.5156C9.77471 21.5156 6.92163 18.6626 6.92163 15.1431C6.92163 15.1347 6.92165 15.1262 6.92168 15.1178C7.2881 17.7998 9.58806 19.8663 12.3707 19.8663C15.4082 19.8663 17.8706 17.4039 17.8706 14.3664C17.8706 11.3288 15.4082 8.86646 12.3707 8.86646C12.302 8.86646 12.2336 8.86771 12.1655 8.87021C12.5318 8.80474 12.909 8.77057 13.2942 8.77057ZM17.0879 14.3664C17.0879 11.7611 14.976 9.64908 12.3707 9.64908C9.7654 9.64908 7.6534 11.7611 7.6534 14.3664C7.6534 16.9716 9.7654 19.0836 12.3707 19.0836C14.976 19.0836 17.0879 16.9716 17.0879 14.3664Z' class='cneutral' fill='%231A1414'%3E%3C/path%3E%3C/svg%3E",
						"size": null
					}
				},
				site_nav: [
					{
						"link": { "url": "/bout", "label": "About" }
					},
					{
						"link": { "url": "/product", "label": "Product" }
					},
					{
						"link": { "url": "/why", "label": "Why" }
					},
					{
						"link": { "url": "/pricing", "label": "Pricing" }
					}
				],
				cta: [
					{
						"link": { "url": "/", "label": "Sign up" }
					}
				]
			}
		});

	component_37 = new Component$C({
			props: {
				quote: {
					"html": "<p>I've been working at the issue of tedius calendar scheduling for years. I finally feel we have a software that solves the real uderlying problems.</p>",
					"markdown": "I've been working at the issue of tedius calendar scheduling for years. I finally feel we have a software that solves the real uderlying problems."
				},
				name: "",
				image: {
					"alt": "Sam, the Founder",
					"src": "https://images.unsplash.com/flagged/photo-1570612861542-284f4c12e75f?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1770&q=80",
					"url": "https://images.unsplash.com/flagged/photo-1570612861542-284f4c12e75f?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1770&q=80",
					"size": null
				}
			}
		});

	component_38 = new Component$D({
			props: {
				superhead: "Testiominals",
				heading: "Hear from our recent users",
				testimonials: [
					{
						"name": "Jess Jones",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1489424731084-a5d8b219a5bb?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjZ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"url": "https://images.unsplash.com/photo-1489424731084-a5d8b219a5bb?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjZ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"size": null
						},
						"quote": {
							"html": "<p>\"Incididunt ipsum elit Lorem Lorem do tempor adipisicing magna laboris labore nostrud magna cillum. Qui quis elit eu officia eu.\" </p>",
							"markdown": "\"Incididunt ipsum elit Lorem Lorem do tempor adipisicing magna laboris labore nostrud magna cillum. Qui quis elit eu officia eu.\" "
						},
						"subtitle": "Director at Expensify"
					},
					{
						"name": "Sal Lane",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1522075469751-3a6694fb2f61?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjJ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"url": "https://images.unsplash.com/photo-1522075469751-3a6694fb2f61?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxzZWFyY2h8MjJ8fHBvcnRyYWl0fGVufDB8fDB8fA%3D%3D&auto=format&fit=crop&w=800&q=60",
							"size": null
						},
						"quote": {
							"html": "<p>\"Proident ad mollit cupidatat enim consequat nisi laborum aliqua. Reprehenderit exercitation laboris consequat sunt occaecat magna sunt velit in occaecat.\" </p>",
							"markdown": "\"Proident ad mollit cupidatat enim consequat nisi laborum aliqua. Reprehenderit exercitation laboris consequat sunt occaecat magna sunt velit in occaecat.\" "
						},
						"subtitle": "Executive at Fintech"
					},
					{
						"name": "Laney Lee",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1597223557154-721c1cecc4b0?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1180&q=80",
							"url": "https://images.unsplash.com/photo-1597223557154-721c1cecc4b0?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=1180&q=80",
							"size": null
						},
						"quote": {
							"html": "<p>\"Aute sint culpa Lorem ipsum mollit do cillum ullamco cupidatat cupidatat ipsum est. Consectetur id nisi pariatur velit qui.\" </p>",
							"markdown": "\"Aute sint culpa Lorem ipsum mollit do cillum ullamco cupidatat cupidatat ipsum est. Consectetur id nisi pariatur velit qui.\" "
						},
						"subtitle": "Developer at Apple"
					},
					{
						"name": "Henry Hue",
						"image": {
							"alt": "",
							"src": "https://images.unsplash.com/photo-1552058544-f2b08422138a?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=798&q=80",
							"url": "https://images.unsplash.com/photo-1552058544-f2b08422138a?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=798&q=80",
							"size": null
						},
						"quote": {
							"html": "<p>\"Nulla esse commodo consectetur dolore exercitation culpa cillum elit. Lorem ut in sit irure tempor id tempor adipisicing labore enim veniam.\" </p>",
							"markdown": "\"Nulla esse commodo consectetur dolore exercitation culpa cillum elit. Lorem ut in sit irure tempor id tempor adipisicing labore enim veniam.\" "
						},
						"subtitle": "Designer at Media Agency"
					}
				]
			}
		});

	component_39 = new Component$E({
			props: {
				heading: "We're moving fast, signup for updates and more.",
				form: {
					"footer": "We'll send you bi-weekly emails about our new features.",
					"placeholder": "Your Email",
					"button_label": "Submit"
				},
				cards: [
					{
						"icon": "mdi:home",
						"title": "User friendly & fun",
						"description": "With a clear intuitive interface, you can easily add and view events."
					},
					{
						"icon": "mdi:home",
						"title": "Responsive and speedy",
						"description": "Our desktop and web application are both super speedy."
					}
				]
			}
		});

	component_40 = new Component$F({});

	component_41 = new Component$G({
			props: {
				heading: "Focus on meeting,<br>not scheduling meetings.",
				subhead: "",
				icon_list: [
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "Open source"
					},
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "Free for individuals"
					},
					{
						"icon": "akar-icons:circle-check-fill",
						"label": "Safe and secure"
					}
				],
				cards: [
					{
						"icon": "material-symbols:check-circle-outline-rounded",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Workflow Automation",
						"content": {
							"html": "<p>Everything you need to get started working real real fast.</p>",
							"markdown": "Everything you need to get started working real real fast."
						}
					},
					{
						"icon": "akar-icons:book",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Double-sided Booking",
						"content": {
							"html": "<p>Its emporium some loremipsum so you can see what it would look like.</p>",
							"markdown": "Its emporium some loremipsum so you can see what it would look like."
						}
					},
					{
						"icon": "akar-icons:calendar",
						"link": { "url": "/", "label": "Learn More" },
						"title": "Calendar Integrations",
						"content": {
							"html": "<p>Its emporium some loremipsum so you can see what it would look like.</p>",
							"markdown": "Its emporium some loremipsum so you can see what it would look like."
						}
					}
				]
			}
		});

	component_42 = new Component$H({
			props: {
				heading: "Your next adventure starts here.",
				subheading: "some text to explain the page or just go with the header.",
				buttons: [
					{
						"link": { "url": "/", "label": "Start here" }
					},
					{ "link": { "url": "/", "label": "Docs" } }
				],
				background: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1473800447596-01729482b8eb?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1740&q=80",
					"url": "https://images.unsplash.com/photo-1473800447596-01729482b8eb?ixlib=rb-4.0.3&ixid=M3wxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8fA%3D%3D&auto=format&fit=crop&w=1740&q=80",
					"size": null
				}
			}
		});

	component_43 = new Component$I({
			props: {
				heading: "Who we've worked with",
				items: [
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"url": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"size": null
						}
					}
				]
			}
		});

	component_44 = new Component$J({
			props: {
				superhead: "Partners",
				heading: "We've gained the trust of loads of companies.",
				logos: [
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/5/5e/Vercel_logo_black.svg/440px-Vercel_logo_black.svg.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"url": "https://upload.wikimedia.org/wikipedia/commons/thumb/9/97/Netlify_logo_%282%29.svg/440px-Netlify_logo_%282%29.svg.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"url": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"url": "https://docs.polyscale.ai/assets/images/supabase-logo-wordmark--light-b617e32c858ef00be44f4e539edb774e.png",
							"size": null
						}
					}
				],
				logo_size: "small"
			}
		});

	component_45 = new Component$K({
			props: {
				superhead: "Features",
				heading: "Offering you something sausy",
				cards: [
					{
						"icon": "material-symbols:where-to-vote-rounded",
						"title": "Accurate GPS",
						"content": {
							"html": "<p>So you know where your friends and loved ones are at all times….</p>",
							"markdown": "So you know where your friends and loved ones are at all times...."
						}
					},
					{
						"icon": "material-symbols:sleep-rounded",
						"title": "Dark Mode Setting",
						"content": {
							"html": "<p>Look at your screen in the dark without disturbing your sleep.</p>",
							"markdown": "Look at your screen in the dark without disturbing your sleep."
						}
					},
					{
						"icon": "material-symbols:chat-bubble-rounded",
						"title": "Real-time Collaboration",
						"content": {
							"html": "<p>Talk whenever you want anywhere, on any device with live updates.</p>",
							"markdown": "Talk whenever you want anywhere, on any device with live updates."
						}
					}
				]
			}
		});

	component_46 = new Component$L({
			props: {
				superhead: "What Drives Us ",
				heading: " We're passionate about building a better meeting workflow",
				content: {
					"html": "<p>Our calendar software company was founded with the goal of helping people better manage their time and stay organized. We recognized that many people struggle to keep track of their busy schedules, and we wanted to provide a simple and effective solution.\nWith our calendar software, we've created an easy-to-use tool that allows users to quickly add and view events, set reminders, and invite others to events. We've also made sure to integrate seamlessly with popular email services, so that users can easily stay connected with their colleagues and friends.</p>",
					"markdown": "Our calendar software company was founded with the goal of helping people better manage their time and stay organized. We recognized that many people struggle to keep track of their busy schedules, and we wanted to provide a simple and effective solution.\nWith our calendar software, we've created an easy-to-use tool that allows users to quickly add and view events, set reminders, and invite others to events. We've also made sure to integrate seamlessly with popular email services, so that users can easily stay connected with their colleagues and friends.\n"
				}
			}
		});

	component_47 = new Component$M({
			props: {
				heading: "Get in touch",
				subheading: "We'd love to hear from you. Drop us a line anytime.",
				inputs: [
					{
						"type": "text",
						"label": "Name",
						"placeholder": "Ad exercitation quis"
					},
					{
						"type": "text",
						"label": "Subject",
						"placeholder": "Mollit nulla veniam"
					},
					{
						"type": "email",
						"label": "Email",
						"placeholder": "Ea ex incididunt"
					},
					{
						"type": "textarea",
						"label": "Message",
						"placeholder": "Dolore lorem adipisicing"
					}
				]
			}
		});

	component_48 = new Component$N({});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
			t10 = space();
			create_component(component_11.$$.fragment);
			t11 = space();
			create_component(component_12.$$.fragment);
			t12 = space();
			create_component(component_13.$$.fragment);
			t13 = space();
			create_component(component_14.$$.fragment);
			t14 = space();
			create_component(component_15.$$.fragment);
			t15 = space();
			create_component(component_16.$$.fragment);
			t16 = space();
			create_component(component_17.$$.fragment);
			t17 = space();
			create_component(component_18.$$.fragment);
			t18 = space();
			create_component(component_19.$$.fragment);
			t19 = space();
			create_component(component_20.$$.fragment);
			t20 = space();
			create_component(component_21.$$.fragment);
			t21 = space();
			create_component(component_22.$$.fragment);
			t22 = space();
			create_component(component_23.$$.fragment);
			t23 = space();
			create_component(component_24.$$.fragment);
			t24 = space();
			create_component(component_25.$$.fragment);
			t25 = space();
			create_component(component_26.$$.fragment);
			t26 = space();
			create_component(component_27.$$.fragment);
			t27 = space();
			create_component(component_28.$$.fragment);
			t28 = space();
			create_component(component_29.$$.fragment);
			t29 = space();
			create_component(component_30.$$.fragment);
			t30 = space();
			create_component(component_31.$$.fragment);
			t31 = space();
			create_component(component_32.$$.fragment);
			t32 = space();
			create_component(component_33.$$.fragment);
			t33 = space();
			create_component(component_34.$$.fragment);
			t34 = space();
			create_component(component_35.$$.fragment);
			t35 = space();
			create_component(component_36.$$.fragment);
			t36 = space();
			create_component(component_37.$$.fragment);
			t37 = space();
			create_component(component_38.$$.fragment);
			t38 = space();
			create_component(component_39.$$.fragment);
			t39 = space();
			create_component(component_40.$$.fragment);
			t40 = space();
			create_component(component_41.$$.fragment);
			t41 = space();
			create_component(component_42.$$.fragment);
			t42 = space();
			create_component(component_43.$$.fragment);
			t43 = space();
			create_component(component_44.$$.fragment);
			t44 = space();
			create_component(component_45.$$.fragment);
			t45 = space();
			create_component(component_46.$$.fragment);
			t46 = space();
			create_component(component_47.$$.fragment);
			t47 = space();
			create_component(component_48.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
			t10 = claim_space(nodes);
			claim_component(component_11.$$.fragment, nodes);
			t11 = claim_space(nodes);
			claim_component(component_12.$$.fragment, nodes);
			t12 = claim_space(nodes);
			claim_component(component_13.$$.fragment, nodes);
			t13 = claim_space(nodes);
			claim_component(component_14.$$.fragment, nodes);
			t14 = claim_space(nodes);
			claim_component(component_15.$$.fragment, nodes);
			t15 = claim_space(nodes);
			claim_component(component_16.$$.fragment, nodes);
			t16 = claim_space(nodes);
			claim_component(component_17.$$.fragment, nodes);
			t17 = claim_space(nodes);
			claim_component(component_18.$$.fragment, nodes);
			t18 = claim_space(nodes);
			claim_component(component_19.$$.fragment, nodes);
			t19 = claim_space(nodes);
			claim_component(component_20.$$.fragment, nodes);
			t20 = claim_space(nodes);
			claim_component(component_21.$$.fragment, nodes);
			t21 = claim_space(nodes);
			claim_component(component_22.$$.fragment, nodes);
			t22 = claim_space(nodes);
			claim_component(component_23.$$.fragment, nodes);
			t23 = claim_space(nodes);
			claim_component(component_24.$$.fragment, nodes);
			t24 = claim_space(nodes);
			claim_component(component_25.$$.fragment, nodes);
			t25 = claim_space(nodes);
			claim_component(component_26.$$.fragment, nodes);
			t26 = claim_space(nodes);
			claim_component(component_27.$$.fragment, nodes);
			t27 = claim_space(nodes);
			claim_component(component_28.$$.fragment, nodes);
			t28 = claim_space(nodes);
			claim_component(component_29.$$.fragment, nodes);
			t29 = claim_space(nodes);
			claim_component(component_30.$$.fragment, nodes);
			t30 = claim_space(nodes);
			claim_component(component_31.$$.fragment, nodes);
			t31 = claim_space(nodes);
			claim_component(component_32.$$.fragment, nodes);
			t32 = claim_space(nodes);
			claim_component(component_33.$$.fragment, nodes);
			t33 = claim_space(nodes);
			claim_component(component_34.$$.fragment, nodes);
			t34 = claim_space(nodes);
			claim_component(component_35.$$.fragment, nodes);
			t35 = claim_space(nodes);
			claim_component(component_36.$$.fragment, nodes);
			t36 = claim_space(nodes);
			claim_component(component_37.$$.fragment, nodes);
			t37 = claim_space(nodes);
			claim_component(component_38.$$.fragment, nodes);
			t38 = claim_space(nodes);
			claim_component(component_39.$$.fragment, nodes);
			t39 = claim_space(nodes);
			claim_component(component_40.$$.fragment, nodes);
			t40 = claim_space(nodes);
			claim_component(component_41.$$.fragment, nodes);
			t41 = claim_space(nodes);
			claim_component(component_42.$$.fragment, nodes);
			t42 = claim_space(nodes);
			claim_component(component_43.$$.fragment, nodes);
			t43 = claim_space(nodes);
			claim_component(component_44.$$.fragment, nodes);
			t44 = claim_space(nodes);
			claim_component(component_45.$$.fragment, nodes);
			t45 = claim_space(nodes);
			claim_component(component_46.$$.fragment, nodes);
			t46 = claim_space(nodes);
			claim_component(component_47.$$.fragment, nodes);
			t47 = claim_space(nodes);
			claim_component(component_48.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			insert_hydration(target, t10, anchor);
			mount_component(component_11, target, anchor);
			insert_hydration(target, t11, anchor);
			mount_component(component_12, target, anchor);
			insert_hydration(target, t12, anchor);
			mount_component(component_13, target, anchor);
			insert_hydration(target, t13, anchor);
			mount_component(component_14, target, anchor);
			insert_hydration(target, t14, anchor);
			mount_component(component_15, target, anchor);
			insert_hydration(target, t15, anchor);
			mount_component(component_16, target, anchor);
			insert_hydration(target, t16, anchor);
			mount_component(component_17, target, anchor);
			insert_hydration(target, t17, anchor);
			mount_component(component_18, target, anchor);
			insert_hydration(target, t18, anchor);
			mount_component(component_19, target, anchor);
			insert_hydration(target, t19, anchor);
			mount_component(component_20, target, anchor);
			insert_hydration(target, t20, anchor);
			mount_component(component_21, target, anchor);
			insert_hydration(target, t21, anchor);
			mount_component(component_22, target, anchor);
			insert_hydration(target, t22, anchor);
			mount_component(component_23, target, anchor);
			insert_hydration(target, t23, anchor);
			mount_component(component_24, target, anchor);
			insert_hydration(target, t24, anchor);
			mount_component(component_25, target, anchor);
			insert_hydration(target, t25, anchor);
			mount_component(component_26, target, anchor);
			insert_hydration(target, t26, anchor);
			mount_component(component_27, target, anchor);
			insert_hydration(target, t27, anchor);
			mount_component(component_28, target, anchor);
			insert_hydration(target, t28, anchor);
			mount_component(component_29, target, anchor);
			insert_hydration(target, t29, anchor);
			mount_component(component_30, target, anchor);
			insert_hydration(target, t30, anchor);
			mount_component(component_31, target, anchor);
			insert_hydration(target, t31, anchor);
			mount_component(component_32, target, anchor);
			insert_hydration(target, t32, anchor);
			mount_component(component_33, target, anchor);
			insert_hydration(target, t33, anchor);
			mount_component(component_34, target, anchor);
			insert_hydration(target, t34, anchor);
			mount_component(component_35, target, anchor);
			insert_hydration(target, t35, anchor);
			mount_component(component_36, target, anchor);
			insert_hydration(target, t36, anchor);
			mount_component(component_37, target, anchor);
			insert_hydration(target, t37, anchor);
			mount_component(component_38, target, anchor);
			insert_hydration(target, t38, anchor);
			mount_component(component_39, target, anchor);
			insert_hydration(target, t39, anchor);
			mount_component(component_40, target, anchor);
			insert_hydration(target, t40, anchor);
			mount_component(component_41, target, anchor);
			insert_hydration(target, t41, anchor);
			mount_component(component_42, target, anchor);
			insert_hydration(target, t42, anchor);
			mount_component(component_43, target, anchor);
			insert_hydration(target, t43, anchor);
			mount_component(component_44, target, anchor);
			insert_hydration(target, t44, anchor);
			mount_component(component_45, target, anchor);
			insert_hydration(target, t45, anchor);
			mount_component(component_46, target, anchor);
			insert_hydration(target, t46, anchor);
			mount_component(component_47, target, anchor);
			insert_hydration(target, t47, anchor);
			mount_component(component_48, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			transition_in(component_11.$$.fragment, local);
			transition_in(component_12.$$.fragment, local);
			transition_in(component_13.$$.fragment, local);
			transition_in(component_14.$$.fragment, local);
			transition_in(component_15.$$.fragment, local);
			transition_in(component_16.$$.fragment, local);
			transition_in(component_17.$$.fragment, local);
			transition_in(component_18.$$.fragment, local);
			transition_in(component_19.$$.fragment, local);
			transition_in(component_20.$$.fragment, local);
			transition_in(component_21.$$.fragment, local);
			transition_in(component_22.$$.fragment, local);
			transition_in(component_23.$$.fragment, local);
			transition_in(component_24.$$.fragment, local);
			transition_in(component_25.$$.fragment, local);
			transition_in(component_26.$$.fragment, local);
			transition_in(component_27.$$.fragment, local);
			transition_in(component_28.$$.fragment, local);
			transition_in(component_29.$$.fragment, local);
			transition_in(component_30.$$.fragment, local);
			transition_in(component_31.$$.fragment, local);
			transition_in(component_32.$$.fragment, local);
			transition_in(component_33.$$.fragment, local);
			transition_in(component_34.$$.fragment, local);
			transition_in(component_35.$$.fragment, local);
			transition_in(component_36.$$.fragment, local);
			transition_in(component_37.$$.fragment, local);
			transition_in(component_38.$$.fragment, local);
			transition_in(component_39.$$.fragment, local);
			transition_in(component_40.$$.fragment, local);
			transition_in(component_41.$$.fragment, local);
			transition_in(component_42.$$.fragment, local);
			transition_in(component_43.$$.fragment, local);
			transition_in(component_44.$$.fragment, local);
			transition_in(component_45.$$.fragment, local);
			transition_in(component_46.$$.fragment, local);
			transition_in(component_47.$$.fragment, local);
			transition_in(component_48.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			transition_out(component_11.$$.fragment, local);
			transition_out(component_12.$$.fragment, local);
			transition_out(component_13.$$.fragment, local);
			transition_out(component_14.$$.fragment, local);
			transition_out(component_15.$$.fragment, local);
			transition_out(component_16.$$.fragment, local);
			transition_out(component_17.$$.fragment, local);
			transition_out(component_18.$$.fragment, local);
			transition_out(component_19.$$.fragment, local);
			transition_out(component_20.$$.fragment, local);
			transition_out(component_21.$$.fragment, local);
			transition_out(component_22.$$.fragment, local);
			transition_out(component_23.$$.fragment, local);
			transition_out(component_24.$$.fragment, local);
			transition_out(component_25.$$.fragment, local);
			transition_out(component_26.$$.fragment, local);
			transition_out(component_27.$$.fragment, local);
			transition_out(component_28.$$.fragment, local);
			transition_out(component_29.$$.fragment, local);
			transition_out(component_30.$$.fragment, local);
			transition_out(component_31.$$.fragment, local);
			transition_out(component_32.$$.fragment, local);
			transition_out(component_33.$$.fragment, local);
			transition_out(component_34.$$.fragment, local);
			transition_out(component_35.$$.fragment, local);
			transition_out(component_36.$$.fragment, local);
			transition_out(component_37.$$.fragment, local);
			transition_out(component_38.$$.fragment, local);
			transition_out(component_39.$$.fragment, local);
			transition_out(component_40.$$.fragment, local);
			transition_out(component_41.$$.fragment, local);
			transition_out(component_42.$$.fragment, local);
			transition_out(component_43.$$.fragment, local);
			transition_out(component_44.$$.fragment, local);
			transition_out(component_45.$$.fragment, local);
			transition_out(component_46.$$.fragment, local);
			transition_out(component_47.$$.fragment, local);
			transition_out(component_48.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
			if (detaching) detach(t10);
			destroy_component(component_11, detaching);
			if (detaching) detach(t11);
			destroy_component(component_12, detaching);
			if (detaching) detach(t12);
			destroy_component(component_13, detaching);
			if (detaching) detach(t13);
			destroy_component(component_14, detaching);
			if (detaching) detach(t14);
			destroy_component(component_15, detaching);
			if (detaching) detach(t15);
			destroy_component(component_16, detaching);
			if (detaching) detach(t16);
			destroy_component(component_17, detaching);
			if (detaching) detach(t17);
			destroy_component(component_18, detaching);
			if (detaching) detach(t18);
			destroy_component(component_19, detaching);
			if (detaching) detach(t19);
			destroy_component(component_20, detaching);
			if (detaching) detach(t20);
			destroy_component(component_21, detaching);
			if (detaching) detach(t21);
			destroy_component(component_22, detaching);
			if (detaching) detach(t22);
			destroy_component(component_23, detaching);
			if (detaching) detach(t23);
			destroy_component(component_24, detaching);
			if (detaching) detach(t24);
			destroy_component(component_25, detaching);
			if (detaching) detach(t25);
			destroy_component(component_26, detaching);
			if (detaching) detach(t26);
			destroy_component(component_27, detaching);
			if (detaching) detach(t27);
			destroy_component(component_28, detaching);
			if (detaching) detach(t28);
			destroy_component(component_29, detaching);
			if (detaching) detach(t29);
			destroy_component(component_30, detaching);
			if (detaching) detach(t30);
			destroy_component(component_31, detaching);
			if (detaching) detach(t31);
			destroy_component(component_32, detaching);
			if (detaching) detach(t32);
			destroy_component(component_33, detaching);
			if (detaching) detach(t33);
			destroy_component(component_34, detaching);
			if (detaching) detach(t34);
			destroy_component(component_35, detaching);
			if (detaching) detach(t35);
			destroy_component(component_36, detaching);
			if (detaching) detach(t36);
			destroy_component(component_37, detaching);
			if (detaching) detach(t37);
			destroy_component(component_38, detaching);
			if (detaching) detach(t38);
			destroy_component(component_39, detaching);
			if (detaching) detach(t39);
			destroy_component(component_40, detaching);
			if (detaching) detach(t40);
			destroy_component(component_41, detaching);
			if (detaching) detach(t41);
			destroy_component(component_42, detaching);
			if (detaching) detach(t42);
			destroy_component(component_43, detaching);
			if (detaching) detach(t43);
			destroy_component(component_44, detaching);
			if (detaching) detach(t44);
			destroy_component(component_45, detaching);
			if (detaching) detach(t45);
			destroy_component(component_46, detaching);
			if (detaching) detach(t46);
			destroy_component(component_47, detaching);
			if (detaching) detach(t47);
			destroy_component(component_48, detaching);
		}
	};
}

class Component$O extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$N, safe_not_equal, {});
	}
}

export default Component$O;
