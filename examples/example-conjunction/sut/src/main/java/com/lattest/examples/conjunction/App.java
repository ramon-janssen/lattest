package com.lattest.examples.conjunction;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Arrays;
import java.util.Random;
import java.util.stream.Collectors;

import com.fasterxml.jackson.core.JsonFactory;
import com.fasterxml.jackson.core.JsonFactoryBuilder;
import com.fasterxml.jackson.core.JsonParseException;
import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.TextNode;

public class App {
	private enum Variant {
		Correct, IncorrectTimeout, IncorrectOutput;
	}
	
	private enum In {
		On, A, B, Take
	}
	private enum Out {
		C, T, CM, TM
	}
	
	static class Implementation {
		public Implementation(Variant variant) {
			this.variant = variant;
		}
		
		private Variant variant;
		private boolean on = false;
		private boolean full = false;
		private boolean coffee = false;
		private boolean tea = false;
		private Random random = new Random(12345);
		
		private void processInput(In in) {
			if (!on) {
				if (in == In.On) {
					on = true; 
				}
			} else if (!full) {
				if (in == In.A) {
					coffee = true;
				} else if (in == In.B) {
					tea = true;
				}
			} else if (full) {
				if (in == In.Take) {
					full = false;
				}
			}
		}
		
		private Out generateOutput() {
			if (coffee) {
				coffee = false;
				return Out.C;
			} else if (tea) {
				tea = false;
				if (random.nextInt(5) == 0) { // 20% chance of a bug
					switch (variant) {
					case IncorrectTimeout:
						return null; // bug: should output C, but doesn't output anything.
					case IncorrectOutput:
						return Out.T; // bug: tea dispenser is out of milk
					default:
						break; // no bug
					}
				}
				return Out.TM;
			}
			return null;
		}
	}
	
    public static void main(String[] args) throws JsonParseException, IOException {
    	Variant variant;
    	if (args.length == 0) {
    		variant = Variant.Correct;
    	} else {
    		try {
    			variant = Variant.valueOf(args[0]);
    		} catch (IllegalArgumentException e) {
    			System.err.println("Unknown program argument '" + args[0] + "'");
    			System.err.println("Allowed program arguments: " + String.join(", ",
    					Arrays.asList(Variant.values()).stream().map(Object::toString).collect(Collectors.toList())));
    			return;
    		}
    	}
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
					Implementation impl = new Implementation(variant);
					TextNode jsonInput;
					do {
						//parser.nextToken();
						for (Out output = impl.generateOutput(); output != null; output = impl.generateOutput()) {
							ByteArrayOutputStream s = new ByteArrayOutputStream();
							mapper.writeValue(s, output);
							s.write('\n');
							out.write(s.toByteArray());
							out.flush();
						}
						System.out.println("reading input");
						jsonInput = mapper.readTree(parser);
						In input;
						if (jsonInput != null) {
							try {
								input = In.valueOf(jsonInput.textValue());
							} catch (Exception e) {
								System.out.println("failed parsing input: " + jsonInput);
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
