
package simpleConcurrent;

import java.util.concurrent.atomic.AtomicReferenceArray;
import java.util.concurrent.atomic.AtomicInteger;

public class ConcurrentArray<V> {
    private final AtomicReferenceArray<V> table;
    private volatile AtomicInteger count;

    public ConcurrentArray() {
        table = new AtomicReferenceArray<V>(32);
        count = new AtomicInteger();
    }

    public void put(int key, V value) {
        if (key < 0 || key >= table.length())
            throw new IndexOutOfBoundsException();
        if (value == null) throw new NullPointerException();
        V oldValue = table.getAndSet(key, value);
        if (oldValue == null)
            count.incrementAndGet();
    }

    public V get(int key) {
        if (key < 0 || key >= table.length())
            throw new IndexOutOfBoundsException();
        return table.get(key);
    }

    public V remove(int key) {
        if (key < 0 || key >= table.length())
            throw new IndexOutOfBoundsException();
        V value = table.getAndSet(key, null);
        if (value != null)
            count.decrementAndGet();
        return value;
    }

    public boolean contains(V value) {
        if (value == null)
            throw new NullPointerException();
        V v;
        for (int k = 0; k < table.length(); k++) {
            v = table.get(k);
            if (v == value || (v != null && value.equals(v)))
              return true;
        }
        return false;
    }

    public int size() {
        return count.get();
    }
/*
    {
      "name": "size",
      "parameters": [],
      "void": false,
      "readonly": true,
      "trusted": true,
      "visibility": "none"
    },
*/

    public boolean isEmpty() {
        return count.get() <= 0;
    }
}

/*

import java.lang.reflect.Array;

public class ConcurrentArray {
    volatile int[] table;

    public ConcurrentArray() {
        int[] t = new int[32];
        table = t;
    }

    public void put(int key, int value) {
        if (key < 0 || key >= table.length)
            throw new IndexOutOfBoundsException();
        table[key] = value;
    }

    public int get(int key) {
        if (key < 0 || key >= table.length)
            throw new IndexOutOfBoundsException();
        return table[key];
    }
}

public class ConcurrentArray<V> {
    volatile V[] table;

    public ConcurrentArray(Class<V> c) {
        @SuppressWarnings("unchecked")
        V[] t = (V[]) Array.newInstance(c, 32);
        table = t;
    }

    public void put(int key, V value) {
        if (key < 0 || key >= table.length)
            throw new IndexOutOfBoundsException();
        table[key] = value;
    }

    public V get(int key) {
        if (key < 0 || key >= table.length)
            throw new IndexOutOfBoundsException();
        return table[key];
    }
}
*/
