package org.lbee.network;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.lbee.protocol.Message;

/**
 * Message box with unordered delivery
 */
public class UnorderedMessageBox implements MessageBox {

    private final List<Message> messages;
    private final Random random;

    public UnorderedMessageBox() {
        messages = new ArrayList<>();
        random = new Random();
    }

    @Override
    public void put(Message message) {
        messages.add(message);
    }

    @Override
    public Message take() {
        if (messages.isEmpty()) {
            return null;
        }

        int rndIdx = random.nextInt(messages.size());
        return messages.remove(rndIdx);
    }
}
