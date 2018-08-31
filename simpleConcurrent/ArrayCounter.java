package simpleConcurrent;

import java.util.concurrent.atomic.AtomicIntegerArray;
import java.util.Random;

public class ArrayCounter {
    private final AtomicIntegerArray table;
    private Random r;
    private static final int tableLength = 32;

    public ArrayCounter() {
        table = new AtomicIntegerArray(tableLength);
        r = new Random();
    }

    public void incr() {
        table.incrementAndGet(r.nextInt(tableLength));
    }

    public void decr() {
        table.decrementAndGet(r.nextInt(tableLength));
    }

    public int get() {
        int count = 0;
        for (int i = 0; i < tableLength; i++) {
            count += table.get(i);
        }
        return count;
    }
}