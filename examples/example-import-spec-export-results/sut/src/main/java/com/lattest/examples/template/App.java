package com.lattest.examples.template;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Random;

import com.fasterxml.jackson.core.JsonFactory;
import com.fasterxml.jackson.core.JsonFactoryBuilder;
import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.TextNode;

public class App {
	private enum State {
		PickEither, Picked1, Picked2, Confirm1, Confirmed1, Confirm2, Confirmed2;
	}
	
	static class Implementation {
		private State state = State.PickEither;
	
		private Random random = new Random(12345);
		 
		private void processInput(String input) {
			switch (state) {
			case Picked1:
				state = State.Confirm1;
				return;
			case Picked2:
				state = State.Confirm2;
				return;
			case Confirmed1:
			case Confirmed2:
				state = State.PickEither;
				return;
			default:
				return;
			}
		}
		
		private String generateOutput() {
			switch (state) {
			case PickEither:
				int out = random.nextInt(2)+1;
				String outStr = String.format("%d_o", out);
				state = out == 1 ? State.Picked1 : State.Picked2;
				return outStr;
			case Confirm1:
				state = State.Confirmed1;
				return "1_o";
			case Confirm2:
				state = State.Confirmed2;
				return "2_o";
			default:
				return null;
			}
		}
	}
	
    public static void main(String[] args) throws JsonParseException, IOException {
        try (ServerSocket server = new ServerSocket(2929)) {
			while (true) {
	        	System.out.println("socket listening on port 2929");
				Socket socket = server.accept();
	        	System.out.println("connection accepted");
	        	if (!socket.isBound()) {
	        		throw new RuntimeException("socket failed to bind to address");
	        	}
				InputStream in = socket.getInputStream();
				OutputStream out = socket.getOutputStream();
				ObjectMapper mapper = new ObjectMapper();
	        	System.out.println("creating parser");
	        	 // charset detection will block parser creation until it read a few bytes of input, which blocks the entire SUT if the input is too short, or if there is no input at all before an output is given first
	        	JsonFactory jf = new JsonFactoryBuilder().configure(JsonFactory.Feature.CHARSET_DETECTION, false).build();	        	
				try (JsonParser parser = jf.createParser((InputStream) in)) {
					Implementation impl = new Implementation();
					TextNode jsonInput;
					do {
						//parser.nextToken();

						State startingState = impl.state;
						startingState = impl.state;
						for (String output = impl.generateOutput(); output != null; output = impl.generateOutput()) {
							ByteArrayOutputStream s = new ByteArrayOutputStream();
							mapper.writeValue(s, output);
							s.write('\n');
							out.write(s.toByteArray());
							out.flush();
							System.out.println(startingState + " ---!" + output + "---> " + impl.state);
							
							startingState = impl.state;
						}
						System.out.println("reading input");
						jsonInput = mapper.readTree(parser);
						String input = "";
						if (jsonInput != null) {
							try {
								input = jsonInput.asText();
								System.out.println("parsed input: " + input);
								System.out.println("(" + startingState + ") ---?" + input + "---> " + impl.state);
							} catch (Exception e) {
								System.out.println("failed parsing input: " + input);
								throw e;
							}
							impl.processInput(input);
						}
					} while(jsonInput != null);
				} catch (Exception e) {
					e.printStackTrace();
				}
		        System.out.println("Connection closed");
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
        System.out.println("Server closed");
    }
}
