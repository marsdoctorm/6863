package org.lbee.network;

import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

import org.lbee.protocol.Message;

/**
 * Message routing bucket for multiple recipients
 */
public class MessageBucket<TMessageBox extends MessageBox> {

    private final ConcurrentHashMap<String, TMessageBox> messageBoxes;
    private final Supplier<TMessageBox> messageBoxCtor;

    public MessageBucket(Supplier<TMessageBox> messageBoxCtor) {
        this.messageBoxes = new ConcurrentHashMap<>();
        this.messageBoxCtor = Objects.requireNonNull(messageBoxCtor);
    }

    public synchronized void put(Message message) {
        messageBoxes.computeIfAbsent(message.getTo(), k -> messageBoxCtor.get())
                .put(message);
    }

    public synchronized Message take(String recipientName) {
        MessageBox messageBox = messageBoxes.get(recipientName);
        return messageBox != null ? messageBox.take() : null;
    }
}
