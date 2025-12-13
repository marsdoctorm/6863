package org.lbee.network;

import org.lbee.protocol.Message;

import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * Message box with FIFO delivery
 */
public class QueueMessageBox implements MessageBox {

    private final Queue<Message> messages;

    public QueueMessageBox() {
        messages = new ConcurrentLinkedQueue<>();
    }

    @Override
    public void put(Message message) {
        messages.add(message);
    }

    @Override
    public Message take() {
        return messages.isEmpty() ? null : messages.poll();
    }
}
